use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};

use crate::validation::{generic_validation_example, validation_check};
use crate::{
    ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA, AgAnalyticReadingV1, AgAssumptionLedgerEntryV1,
    AgStructuralVerdictV1, AgVerdictDataV1, ArchSigMeasurementPacketV1, LawPolicyDocumentV1,
    MeasurementProfileV1, NormalizedArchMapV2, NormalizedAtomV2, NormalizedContextV2,
    NormalizedCoverV2, ValidationCheck, ValidationExample,
};

const VERDICTS: [&str; 5] = [
    "measured_zero",
    "measured_nonzero",
    "unmeasured",
    "unknown",
    "not_computed",
];
const MAX_SQUARE_FREE_WITNESS_VARIABLES: usize = 12;
const MAX_TOR_WITNESS_VARIABLES: usize = 12;
const MAX_LAPLACIAN_CELLS: usize = 16;
const MAX_PERIOD_CYCLES: usize = 16;
const MAX_TRANSFER_TARGETS: usize = 16;
const GLUING_TRIANGLE_RENDER_LIMIT: usize = 80;
const GLUING_FIELD_ROW_RENDER_LIMIT: usize = 64;
const GLUING_REGION_RENDER_LIMIT: usize = 24;
const GLUING_CAGE_RENDER_LIMIT: usize = 80;
const GLUING_MORPH_RENDER_LIMIT: usize = 50;
const GLUING_ATOM_GLYPH_RENDER_LIMIT: usize = 2_000;

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
    let mut analytic_readings = vec![AgAnalyticReadingV1 {
        reading_id: "candidate-regime:stability-placeholder".to_string(),
        evaluator: "ag.foundation@1".to_string(),
        value: json!({
            "state": "not_evaluated",
            "reason": "theorem-candidate readings are analytic-only until a follow-up evaluator computes them"
        }),
        regime: Some("theorem-candidate".to_string()),
        structural_verdict_ref: None,
    }];
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
        } else if evaluator == "ag.law-conflict-tor@1" {
            validate_tor_profile_v1(&profile)?;
            let measurement = evaluate_law_conflict_tor_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.law-conflict-tor".to_string()),
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
        } else if evaluator == "ag.sheaf-laplacian@1" {
            validate_laplacian_profile_v1(&profile)?;
            let measurement = evaluate_sheaf_laplacian_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.sheaf-laplacian".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: false,
                    non_zero: false,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.period-stokes@1" {
            validate_period_profile_v1(&profile)?;
            let measurement = evaluate_period_stokes_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
        } else if evaluator == "ag.support-transfer@1" {
            validate_transfer_profile_v1(&profile)?;
            let measurement = evaluate_support_transfer_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
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
        analytic_readings,
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
    nsdepth: Option<usize>,
    support_atom_refs: Vec<String>,
    verified_minimal_forbidden_supports: Vec<Vec<String>>,
    status: String,
    effect: String,
}

#[derive(Debug, Clone)]
struct TorMeasurementV1 {
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
struct TorCommonAmbientV1 {
    ambient_ref: String,
    atom_ref: String,
    law_pair: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TorIdealGeneratorV1 {
    law: String,
    generator_id: String,
    support: Vec<String>,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TorConflictClassV1 {
    conflict_id: String,
    degree: usize,
    support: Vec<String>,
    shared_support: Vec<String>,
    left_law: String,
    left_generator_ref: String,
    right_law: String,
    right_generator_ref: String,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct LaplacianMeasurementV1 {
    verdict: String,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
    computed_invariants: Vec<Value>,
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct LaplacianCellV1 {
    cell_id: String,
    value: f64,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct LaplacianEdgeV1 {
    source: String,
    target: String,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct PeriodMeasurementV1 {
    computed_invariants: Vec<Value>,
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct PeriodIntegralV1 {
    form_id: String,
    cycle_id: String,
    value: f64,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct StokesAuditValueV1 {
    form_id: String,
    chain_id: String,
    value: f64,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TransferMeasurementV1 {
    computed_invariants: Vec<Value>,
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct TransferPairingV1 {
    path_id: String,
    target_id: String,
    value: f64,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TransferRepairPathV1 {
    path_id: String,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TransferGroundCostV1 {
    target_id: String,
    cost: f64,
    atom_ref: String,
    source_refs: Vec<String>,
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
    let certificate = square_free_certificate(
        normalized,
        &selected_contexts,
        &minimal_forbidden_supports,
        &repair_hitting_sets,
        &generators,
        witness_variables.len(),
    )?;
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
        if certificate.status == "verified" {
            (
                "measured_nonzero".to_string(),
                false,
                true,
                "nsdepth_certificate_verified".to_string(),
                Some(certificate.cert_ref.clone()),
                "square-free obstruction generators were found and the selected finite NSdepth certificate payload matches the computed obstruction ideal".to_string(),
            )
        } else {
            (
                "unknown".to_string(),
                false,
                false,
                format!("nsdepth_certificate_{}", certificate.status),
                Some(certificate.cert_ref.clone()),
                certificate.effect.clone(),
            )
        }
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
                "status": certificate.status,
                "certificateRef": certificate.cert_ref,
                "nsdepth": certificate.nsdepth,
                "supportAtomRefs": certificate.support_atom_refs,
                "verifiedMinimalForbiddenSupports": certificate.verified_minimal_forbidden_supports,
                "effect": certificate.effect
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
                assumption: "NSdepth certificate payload covers the computed square-free obstruction ideal within the selected witness family".to_string(),
                status: certificate
                    .as_ref()
                    .filter(|certificate| certificate.status == "verified")
                    .map(|_| "checked")
                    .unwrap_or("assumed")
                    .to_string(),
                checked_by: certificate
                    .as_ref()
                    .filter(|certificate| certificate.status == "verified")
                    .map(|certificate| format!("ag.square-free-repair@1:{}", certificate.cert_ref)),
                assumed_by: certificate
                    .as_ref()
                    .map(|certificate| {
                        if certificate.status == "verified" {
                            None
                        } else {
                            Some(certificate.cert_ref.clone())
                        }
                    })
                    .unwrap_or_else(|| Some(format!("measurement-profile:{}", profile.profile_id))),
            },
        ],
    })
}

fn evaluate_law_conflict_tor_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<TorMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let witness_variables = tor_witness_variables(profile);
    let ambient = tor_common_ambient(normalized, &selected_contexts)?;
    let Some(ambient) = ambient else {
        return Ok(TorMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "no_common_ambient".to_string(),
            cert_ref: None,
            reason: "common ambient pair is not supplied; no LawConflict comparison is computed"
                .to_string(),
            computed_invariants: vec![json!({
                "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
                "evaluator": "ag.law-conflict-tor@1",
                "method": "finite-monomial-tor@1",
                "selectedCoverRef": profile.cover_ref,
                "status": "not_computed",
                "reason": "no_common_ambient"
            })],
            assumptions: tor_assumptions(profile, None, "violated"),
        });
    };

    let generators = tor_ideal_generators(normalized, &selected_contexts, &witness_variables)?;
    let law_order = ambient.law_pair.clone();
    let selected_laws = generators
        .iter()
        .map(|generator| generator.law.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let ambient_laws = law_order.iter().cloned().collect::<BTreeSet<_>>();
    let outside_ambient = selected_laws
        .iter()
        .filter(|law| !ambient_laws.contains(*law))
        .cloned()
        .collect::<Vec<_>>();
    if !outside_ambient.is_empty() {
        return Err(format!(
            "ag.law-conflict-tor@1 selected law generators outside common ambient pair: {}",
            outside_ambient.join(",")
        ));
    }
    if selected_laws.len() != 2 || selected_laws != law_order {
        return Err(format!(
            "ag.law-conflict-tor@1 requires generators for exactly the common ambient law pair {}, found {}",
            law_order.join(","),
            selected_laws.join(",")
        ));
    }
    let conflicts = tor_conflict_classes(&generators, &law_order[0], &law_order[1]);
    let has_conflict = !conflicts.is_empty();
    let law_ideals = law_order
        .iter()
        .map(|law| {
            json!({
                "law": law,
                "generators": generators.iter()
                    .filter(|generator| &generator.law == law)
                    .map(|generator| json!({
                        "generatorId": generator.generator_id,
                        "support": generator.support,
                        "contextRefs": generator.context_refs,
                        "sourceRefs": generator.source_refs
                    }))
                    .collect::<Vec<_>>()
            })
        })
        .collect::<Vec<_>>();
    let conflict_json = conflicts
        .iter()
        .map(|conflict| {
            json!({
                "conflictId": conflict.conflict_id,
                "degree": conflict.degree,
                "support": conflict.support,
                "sharedSupport": conflict.shared_support,
                "leftLaw": conflict.left_law,
                "leftGeneratorRef": conflict.left_generator_ref,
                "rightLaw": conflict.right_law,
                "rightGeneratorRef": conflict.right_generator_ref,
                "contextRefs": conflict.context_refs,
                "sourceRefs": conflict.source_refs
            })
        })
        .collect::<Vec<_>>();

    Ok(TorMeasurementV1 {
        verdict: if has_conflict {
            "measured_nonzero".to_string()
        } else {
            "measured_zero".to_string()
        },
        zero: !has_conflict,
        non_zero: has_conflict,
        method_status: "finite_degree1_shared_support_conflict_computed".to_string(),
        cert_ref: Some(ambient.atom_ref.clone()),
        reason: if has_conflict {
            "finite degree-1 shared-support detector found LawConflict classes under the supplied common ambient"
                .to_string()
        } else {
            "finite degree-1 shared-support detector found no LawConflict class under the supplied common ambient"
                .to_string()
        },
        computed_invariants: vec![json!({
                "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
                "evaluator": "ag.law-conflict-tor@1",
                "method": "finite-degree1-shared-support-conflict@1",
                "claimScope": "degree-1 shared-support conflict detector over the selected common ambient pair",
                "resolution": profile.resolution_selector,
            "selectedCoverRef": profile.cover_ref,
            "witnessVariables": witness_variables,
            "commonAmbient": {
                "ambientRef": ambient.ambient_ref,
                "atomRef": ambient.atom_ref,
                "lawPair": ambient.law_pair,
                "sourceRefs": ambient.source_refs
            },
            "lawIdeals": law_ideals,
            "lawConflicts": conflict_json,
            "torByDegree": [{
                "degree": 1,
                "classCount": conflicts.len(),
                "scope": "detected shared witness-variable support only"
            }],
            "nonConclusions": [
                "This evaluator does not compute a full Taylor, Scarf, or free resolution Tor algebra.",
                "Flat base change stability is a theorem-candidate reading and is not concluded by this structural verdict."
            ]
        })],
        assumptions: tor_assumptions(profile, Some(&ambient), "checked"),
    })
}

fn evaluate_sheaf_laplacian_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<LaplacianMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let witness_variables = laplacian_witness_variables(profile);
    let cells = laplacian_cells(normalized, &selected_contexts, &witness_variables)?;
    let edges = laplacian_edges(normalized, &selected_contexts)?;
    let observed_cells = cells
        .iter()
        .map(|cell| cell.cell_id.clone())
        .collect::<BTreeSet<_>>();
    let missing_cells = witness_variables
        .iter()
        .filter(|cell| !observed_cells.contains(*cell))
        .cloned()
        .collect::<Vec<_>>();
    if cells.is_empty() || edges.is_empty() || !missing_cells.is_empty() {
        let reason = if missing_cells.is_empty() {
            "cellular_model_missing".to_string()
        } else {
            format!("cellular_model_missing:{}", missing_cells.join(","))
        };
        return Ok(LaplacianMeasurementV1 {
            verdict: "not_computed".to_string(),
            method_status: "cellular_model_missing".to_string(),
            cert_ref: None,
            reason: "selected cellular cochains or boundaries are missing; no Laplacian analytic reading is computed".to_string(),
            computed_invariants: vec![json!({
                "invariantId": format!("sheaf-laplacian:{}", profile.profile_id),
                "evaluator": "ag.sheaf-laplacian@1",
                "status": "not_computed",
                "reason": reason
            })],
            analytic_readings: Vec::new(),
            assumptions: laplacian_assumptions(profile, "violated"),
        });
    }

    let cell_ids = cells
        .iter()
        .map(|cell| cell.cell_id.clone())
        .collect::<Vec<_>>();
    let cell_index = cell_ids
        .iter()
        .enumerate()
        .map(|(index, cell)| (cell.clone(), index))
        .collect::<BTreeMap<_, _>>();
    for edge in &edges {
        if !cell_index.contains_key(&edge.source) || !cell_index.contains_key(&edge.target) {
            return Err(format!(
                "ag.sheaf-laplacian@1 boundary {} references cells outside selected cochain family",
                edge.atom_ref
            ));
        }
    }
    let laplacian = graph_laplacian(&cell_ids, &cell_index, &edges);
    let cochain = cells.iter().map(|cell| cell.value).collect::<Vec<_>>();
    let components = graph_components(cell_ids.len(), &cell_index, &edges);
    let harmonic = harmonic_projection(&cochain, &components);
    let exact = vec![0.0; cochain.len()];
    let coexact = cochain
        .iter()
        .zip(harmonic.iter())
        .map(|(value, harmonic)| value - harmonic)
        .collect::<Vec<_>>();
    let harmonic_mass = squared_norm(&harmonic);
    let distance_to_flatness = squared_norm(&coexact);
    let eigenvalues = jacobi_eigenvalues_symmetric(laplacian.clone());
    let spectral_gap = eigenvalues
        .iter()
        .copied()
        .filter(|value| *value > 1.0e-9)
        .fold(None, |best: Option<f64>, value| {
            Some(best.map_or(value, |best| best.min(value)))
        })
        .unwrap_or(0.0);
    let curvature_transfer = laplacian
        .iter()
        .enumerate()
        .map(|(index, row)| {
            let value = row
                .iter()
                .zip(cochain.iter())
                .map(|(entry, cochain)| entry * cochain)
                .sum::<f64>();
            json!({
                "cell": cell_ids[index],
                "curvature": round_f64(value)
            })
        })
        .collect::<Vec<_>>();
    let source_refs = cells
        .iter()
        .flat_map(|cell| cell.source_refs.iter())
        .chain(edges.iter().flat_map(|edge| edge.source_refs.iter()))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    let analytic_value = json!({
        "readingKind": "graph-laplacian-hodge-proxy@1",
        "modelScope": "finite graph Laplacian over selected cochain cells and boundary edges",
        "selectedCoverRef": profile.cover_ref,
        "cells": cell_ids,
        "cochain": rounded_vec(&cochain),
        "hodgeDecomposition": {
            "exact": rounded_vec(&exact),
            "harmonic": rounded_vec(&harmonic),
            "coexact": rounded_vec(&coexact)
        },
        "harmonicMass": round_f64(harmonic_mass),
        "distanceToFlatness": round_f64(distance_to_flatness),
        "spectralGap": round_f64(spectral_gap),
        "curvatureTransferSpectrum": curvature_transfer,
        "nonConclusion": "near-flat analytic values are not structural lawfulness verdicts"
    });

    Ok(LaplacianMeasurementV1 {
        verdict: "unknown".to_string(),
        method_status: "finite_laplacian_analytic_reading_computed".to_string(),
        cert_ref: None,
        reason: "finite Laplacian / Hodge values were computed as analytic readings; structural lawfulness is not concluded".to_string(),
        computed_invariants: vec![json!({
            "invariantId": format!("sheaf-laplacian:{}", profile.profile_id),
            "evaluator": "ag.sheaf-laplacian@1",
            "method": "finite-graph-laplacian@1",
            "claimScope": "graph Laplacian analytic proxy; not a full sheaf chain-complex Hodge theorem",
            "selectedCoverRef": profile.cover_ref,
            "cellRefs": cells.iter().map(|cell| json!({
                "cell": cell.cell_id,
                "cochainAtomRef": cell.atom_ref
            })).collect::<Vec<_>>(),
            "laplacianMatrix": rounded_matrix(&laplacian),
            "sourceRefs": source_refs
        })],
        analytic_readings: vec![
            AgAnalyticReadingV1 {
                reading_id: format!("analytic:sheaf-laplacian:{}", profile.profile_id),
                evaluator: "ag.sheaf-laplacian@1".to_string(),
                value: analytic_value,
                regime: Some("analytic-measurement".to_string()),
                structural_verdict_ref: None,
            },
            AgAnalyticReadingV1 {
                reading_id: format!("theorem-candidate:harmonic-debt:{}", profile.profile_id),
                evaluator: "ag.foundation@1".to_string(),
                value: json!({
                    "readingKind": "harmonic-debt-minimality-candidate@1",
                    "essentialRepairLowerBound": round_f64(distance_to_flatness.sqrt()),
                    "reason": "harmonic debt minimality remains theorem-candidate and cannot generate a structural verdict"
                }),
                regime: Some("theorem-candidate".to_string()),
                structural_verdict_ref: None,
            },
        ],
        assumptions: laplacian_assumptions(profile, "checked"),
    })
}

fn evaluate_period_stokes_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<PeriodMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let cycle_basis = period_witness_cycles(profile);
    let pairings = period_integrals(normalized, &selected_contexts, &cycle_basis)?;
    let d_omega = stokes_audit_values(
        normalized,
        &selected_contexts,
        "dOmegaIntegral",
        "ag.period-stokes@1 d omega audit",
    )?;
    let boundary = stokes_audit_values(
        normalized,
        &selected_contexts,
        "boundaryPeriod",
        "ag.period-stokes@1 boundary audit",
    )?;
    let observed_cycles = pairings
        .iter()
        .map(|pairing| pairing.cycle_id.clone())
        .collect::<BTreeSet<_>>();
    let missing_cycles = cycle_basis
        .iter()
        .filter(|cycle| !observed_cycles.contains(*cycle))
        .cloned()
        .collect::<Vec<_>>();
    if pairings.is_empty()
        || d_omega.is_empty()
        || boundary.is_empty()
        || !missing_cycles.is_empty()
    {
        let reason = if missing_cycles.is_empty() {
            "period_model_missing".to_string()
        } else {
            format!("period_model_missing:{}", missing_cycles.join(","))
        };
        return Ok(PeriodMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("period-stokes:{}", profile.profile_id),
                "evaluator": "ag.period-stokes@1",
                "status": "not_computed",
                "reason": reason
            })],
            analytic_readings: Vec::new(),
            assumptions: period_assumptions(profile, "violated"),
        });
    }

    let forms = pairings
        .iter()
        .map(|pairing| pairing.form_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let observed_pairings = pairings
        .iter()
        .map(|pairing| (pairing.form_id.clone(), pairing.cycle_id.clone()))
        .collect::<BTreeSet<_>>();
    let mut missing_pairings = Vec::new();
    for form in &forms {
        for cycle in &cycle_basis {
            if !observed_pairings.contains(&(form.clone(), cycle.clone())) {
                missing_pairings.push(format!("{form}/{cycle}"));
            }
        }
    }
    if !missing_pairings.is_empty() {
        return Ok(PeriodMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("period-stokes:{}", profile.profile_id),
                "evaluator": "ag.period-stokes@1",
                "status": "not_computed",
                "reason": format!("period_model_missing:{}", missing_pairings.join(","))
            })],
            analytic_readings: Vec::new(),
            assumptions: period_assumptions(profile, "violated"),
        });
    }
    let form_index = forms
        .iter()
        .enumerate()
        .map(|(index, form)| (form.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let cycle_index = cycle_basis
        .iter()
        .enumerate()
        .map(|(index, cycle)| (cycle.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut matrix = vec![vec![0.0; cycle_basis.len()]; forms.len()];
    for pairing in &pairings {
        matrix[form_index[&pairing.form_id]][cycle_index[&pairing.cycle_id]] = pairing.value;
    }
    let audit = stokes_audit_report(&d_omega, &boundary)?;
    let source_refs = pairings
        .iter()
        .flat_map(|pairing| pairing.source_refs.iter())
        .chain(d_omega.iter().flat_map(|entry| entry.source_refs.iter()))
        .chain(boundary.iter().flat_map(|entry| entry.source_refs.iter()))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    let analytic_value = json!({
        "readingKind": "strict-period-pairing@1",
        "selectedCoverRef": profile.cover_ref,
        "modelRelative": true,
        "forms": forms,
        "cycleBasis": cycle_basis,
        "periodPairingMatrix": rounded_matrix(&matrix),
        "stokesAudit": audit,
        "nonConclusion": "period pairing is a model-relative analytic reading and is not a structural lawfulness verdict"
    });

    Ok(PeriodMeasurementV1 {
        computed_invariants: vec![json!({
            "invariantId": format!("period-stokes:{}", profile.profile_id),
            "evaluator": "ag.period-stokes@1",
            "method": "finite-poset-period-stokes@1",
            "selectedCoverRef": profile.cover_ref,
            "pairingAtomRefs": pairings.iter().map(|pairing| json!({
                "form": pairing.form_id,
                "cycle": pairing.cycle_id,
                "atomRef": pairing.atom_ref
            })).collect::<Vec<_>>(),
            "periodPairingMatrix": rounded_matrix(&matrix),
            "stokesAudit": audit,
            "sourceRefs": source_refs
        })],
        analytic_readings: vec![AgAnalyticReadingV1 {
            reading_id: format!("analytic:period-stokes:{}", profile.profile_id),
            evaluator: "ag.period-stokes@1".to_string(),
            value: analytic_value,
            regime: Some("analytic-measurement".to_string()),
            structural_verdict_ref: None,
        }],
        assumptions: period_assumptions(profile, "checked"),
    })
}

fn evaluate_support_transfer_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<TransferMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let targets = transfer_witness_targets(profile);
    let repair_paths = transfer_repair_paths(normalized, &selected_contexts)?;
    let pairings = transfer_pairings(normalized, &selected_contexts, &targets)?;
    let ground_costs = transfer_ground_costs(normalized, &selected_contexts, &targets)?;
    let observed_targets = pairings
        .iter()
        .map(|pairing| pairing.target_id.clone())
        .collect::<BTreeSet<_>>();
    let missing_targets = targets
        .iter()
        .filter(|target| !observed_targets.contains(*target))
        .cloned()
        .collect::<Vec<_>>();
    let cost_targets = ground_costs
        .iter()
        .map(|cost| cost.target_id.clone())
        .collect::<BTreeSet<_>>();
    let missing_costs = targets
        .iter()
        .filter(|target| !cost_targets.contains(*target))
        .cloned()
        .collect::<Vec<_>>();
    if repair_paths.is_empty()
        || pairings.is_empty()
        || ground_costs.is_empty()
        || !missing_targets.is_empty()
        || !missing_costs.is_empty()
    {
        let mut reasons = Vec::new();
        if repair_paths.is_empty() || pairings.is_empty() || ground_costs.is_empty() {
            reasons.push("transfer_model_missing".to_string());
        }
        if !missing_targets.is_empty() {
            reasons.push(format!("missing_pairings:{}", missing_targets.join(",")));
        }
        if !missing_costs.is_empty() {
            reasons.push(format!("missing_ground_costs:{}", missing_costs.join(",")));
        }
        return Ok(TransferMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("support-transfer:{}", profile.profile_id),
                "evaluator": "ag.support-transfer@1",
                "status": "not_computed",
                "reason": reasons.join(";")
            })],
            analytic_readings: Vec::new(),
            assumptions: transfer_assumptions(profile, "violated"),
        });
    }

    let paths = repair_paths
        .iter()
        .map(|path| path.path_id.clone())
        .collect::<Vec<_>>();
    let path_set = paths.iter().cloned().collect::<BTreeSet<_>>();
    let outside_paths = pairings
        .iter()
        .filter(|pairing| !path_set.contains(&pairing.path_id))
        .map(|pairing| pairing.path_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if !outside_paths.is_empty() {
        return Err(format!(
            "ag.support-transfer@1 transfer pairings reference paths outside selected repair path model: {}",
            outside_paths.join(",")
        ));
    }
    let observed_pairings = pairings
        .iter()
        .map(|pairing| (pairing.path_id.clone(), pairing.target_id.clone()))
        .collect::<BTreeSet<_>>();
    let mut missing_pairings = Vec::new();
    for path in &paths {
        for target in &targets {
            if !observed_pairings.contains(&(path.clone(), target.clone())) {
                missing_pairings.push(format!("{path}/{target}"));
            }
        }
    }
    if !missing_pairings.is_empty() {
        return Ok(TransferMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("support-transfer:{}", profile.profile_id),
                "evaluator": "ag.support-transfer@1",
                "status": "not_computed",
                "reason": format!("transfer_model_missing:{}", missing_pairings.join(","))
            })],
            analytic_readings: Vec::new(),
            assumptions: transfer_assumptions(profile, "violated"),
        });
    }

    let path_index = paths
        .iter()
        .enumerate()
        .map(|(index, path)| (path.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let target_index = targets
        .iter()
        .enumerate()
        .map(|(index, target)| (target.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut matrix = vec![vec![0.0; targets.len()]; paths.len()];
    for pairing in &pairings {
        matrix[path_index[&pairing.path_id]][target_index[&pairing.target_id]] = pairing.value;
    }
    let cost_by_target = ground_costs
        .iter()
        .map(|cost| (cost.target_id.clone(), cost.cost))
        .collect::<BTreeMap<_, _>>();
    let transfer_residue = matrix
        .iter()
        .flatten()
        .map(|value| value * value)
        .sum::<f64>()
        .sqrt();
    let wasserstein_cost = pairings
        .iter()
        .map(|pairing| pairing.value.abs() * cost_by_target[&pairing.target_id])
        .sum::<f64>();
    let source_refs = pairings
        .iter()
        .flat_map(|pairing| pairing.source_refs.iter())
        .chain(repair_paths.iter().flat_map(|path| path.source_refs.iter()))
        .chain(ground_costs.iter().flat_map(|cost| cost.source_refs.iter()))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    let analytic_value = json!({
        "readingKind": "support-localized-transfer@1",
        "selectedCoverRef": profile.cover_ref,
        "modelRelative": true,
        "repairPaths": paths,
        "transferTargets": targets,
        "transferMeasurementPairing": rounded_matrix(&matrix),
        "transferResidue": round_f64(transfer_residue),
        "wassersteinTransferCost": round_f64(wasserstein_cost),
        "groundCosts": ground_costs.iter().map(|cost| json!({
            "target": cost.target_id,
            "cost": round_f64(cost.cost),
            "atomRef": cost.atom_ref
        })).collect::<Vec<_>>(),
        "nonConclusion": "transfer readings do not prove absence of side effects or global repair safety"
    });

    Ok(TransferMeasurementV1 {
        computed_invariants: vec![json!({
            "invariantId": format!("support-transfer:{}", profile.profile_id),
            "evaluator": "ag.support-transfer@1",
            "method": "finite-support-localized-transfer@1",
            "selectedCoverRef": profile.cover_ref,
            "repairPathAtomRefs": repair_paths.iter().map(|path| json!({
                "repairPath": path.path_id,
                "atomRef": path.atom_ref
            })).collect::<Vec<_>>(),
            "pairingAtomRefs": pairings.iter().map(|pairing| json!({
                "repairPath": pairing.path_id,
                "target": pairing.target_id,
                "atomRef": pairing.atom_ref
            })).collect::<Vec<_>>(),
            "transferMeasurementPairing": rounded_matrix(&matrix),
            "transferResidue": round_f64(transfer_residue),
            "wassersteinTransferCost": round_f64(wasserstein_cost),
            "sourceRefs": source_refs
        })],
        analytic_readings: vec![
            AgAnalyticReadingV1 {
                reading_id: format!("analytic:support-transfer:{}", profile.profile_id),
                evaluator: "ag.support-transfer@1".to_string(),
                value: analytic_value,
                regime: Some("analytic-measurement".to_string()),
                structural_verdict_ref: None,
            },
            AgAnalyticReadingV1 {
                reading_id: format!(
                    "theorem-candidate:transfer-lower-bound:{}",
                    profile.profile_id
                ),
                evaluator: "ag.foundation@1".to_string(),
                value: json!({
                    "readingKind": "transfer-lower-bound-candidate@1",
                    "transferLowerBound": round_f64(wasserstein_cost),
                    "reason": "transfer lower bound remains theorem-candidate and cannot generate a structural verdict"
                }),
                regime: Some("theorem-candidate".to_string()),
                structural_verdict_ref: None,
            },
        ],
        assumptions: transfer_assumptions(profile, "checked"),
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
    } else if packet.structural_verdict.is_empty() {
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    } else if nonzero_count == 0 {
        "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    } else {
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    };
    json!({
        "schema": "archsig-analysis-summary/v2",
        "conclusion": conclusion,
        "readThisFirst": {
            "heading": "Read this first",
            "conclusion": conclusion,
            "whatItMeans": if cech_nonzero {
                "Local rules are not enough to explain the selected cover; ArchSig measured a cross-context glue mismatch."
            } else if nonzero_count > 0 {
                "ArchSig measured a selected AG obstruction under the profile."
            } else if unmeasured_count > 0 {
                "ArchSig produced a profile-relative foundation result with unmeasured, unknown, or not_computed rows still visible."
            } else {
                "No selected H1 glue mismatch was measured under the profile."
            },
            "whereToLookFirst": "See archsig-insight-report.json#/insightCards/0/evidence",
            "nextAction": "Open archsig-insight-brief.md or the viewer Insight Queue.",
            "boundary": format!(
                "Profile-relative. {} assumptions declared. {} non-terminal rows.",
                packet.assumptions.iter().filter(|row| row.status == "assumed").count(),
                unmeasured_count
            )
        },
        "measurementPacketSchema": packet.schema,
        "profileRef": packet.profile.profile_id,
        "insightArtifacts": {
            "insightReport": "archsig-insight-report.json",
            "insightBrief": "archsig-insight-brief.md",
            "viewerData": "archsig-atom-viewer-data.json"
        },
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

pub fn build_insight_report_v1(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    summary: &Value,
) -> Value {
    let boundary_digest = insight_boundary_digest(packet, summary);
    let insight_cards = insight_cards_v1(normalized, packet, summary);
    let action_queue = insight_action_queue_v1(&insight_cards);
    let gluing_geometry = gluing_geometry_projection_v1(normalized, packet);
    let viewer_visual_scenes =
        insight_viewer_visual_scenes_v1(normalized, packet, &insight_cards, &gluing_geometry);
    let guided_tours = insight_guided_tours_v1(&insight_cards);
    let copy_blocks = insight_copy_blocks_v1(normalized, &insight_cards, &boundary_digest);
    let omitted_detail_counts = insight_omitted_detail_counts_v1(normalized, &viewer_visual_scenes);
    let top_card = insight_cards.first().cloned().unwrap_or_else(|| {
        json!({
            "id": "insight:measurement-boundary:empty",
            "kind": "measurement_boundary",
            "severity": "info",
            "title": "Measurement boundary recorded",
            "oneLine": "ArchSig generated a bounded measurement projection under the selected profile.",
            "whyItMatters": "Reviewers can inspect the selected profile, assumptions, and artifact links before reading details.",
            "evidence": empty_insight_evidence(),
            "nextAction": {
                "label": "Inspect measurement boundary",
                "kind": "inspect",
                "targetRefs": ["boundary-digest:main"]
            },
            "viewerNavigation": {
                "sceneId": "boundary-assumption",
                "highlightRefs": empty_highlight_refs()
            },
            "tourRefs": ["tour:measurement-boundary:empty"],
            "rankingBasis": ["fallback boundary reading"],
            "nonClaims": ["This does not add a new measurement claim."]
        })
    });
    json!({
        "schema": "archsig-insight-report/v1",
        "reportId": format!("insight:{}", packet.packet_id),
        "sourcePacketRef": "archsig-measurement-packet.json",
        "generatedAt": "deterministic-run-artifact",
        "outputArtifacts": {
            "summaryRef": "archsig-analysis-summary.json",
            "briefRef": "archsig-insight-brief.md",
            "viewerDataRef": "archsig-atom-viewer-data.json"
        },
        "headline": {
            "conclusionCode": summary["conclusion"],
            "title": top_card["title"],
            "summary": top_card["oneLine"],
            "decisionState": insight_decision_state(&top_card),
            "primaryVerdictRefs": top_card["evidence"]["structuralVerdictRefs"],
            "boundaryDigestRef": "boundary-digest:main"
        },
        "readThisFirst": {
            "heading": "Read this first",
            "conclusion": summary["conclusion"],
            "whatItMeans": top_card["oneLine"],
            "whereToLookFirst": top_card["evidence"]["sourceRefs"],
            "nextAction": top_card["nextAction"]["label"],
            "boundary": boundary_digest["shortText"],
            "details": top_card["evidence"]
        },
        "insightCards": insight_cards,
        "actionQueue": action_queue,
        "boundaryDigest": boundary_digest,
        "omittedDetailCounts": omitted_detail_counts,
        "gluingGeometry": gluing_geometry,
        "viewerVisualScenes": viewer_visual_scenes,
        "guidedTours": guided_tours,
        "copyBlocks": copy_blocks,
        "rankingBasis": [
            "validation_failure",
            "measured_nonzero structural verdict",
            "not_computed due to violated assumption",
            "repair lower bound or minimal repair candidate",
            "policy conflict",
            "architecture debt mass analytic reading",
            "measurement boundary",
            "measured_zero confirmation"
        ],
        "claimValidation": {
            "measuredClaimsRequireStructuralVerdictRefs": true,
            "analyticReadingsDoNotPromoteLawfulOrUnlawful": true,
            "highSeverityInsightsRequireWhereRefs": true,
            "notComputedBlockersRequireReasonCode": true,
            "repairCandidatesRequireNonClaims": true,
            "theoremCandidatePromotionForbidden": true,
            "monodromyVerdictGenerated": false
        },
        "nonConclusions": [
            "Insight report is a projection of archsig-measurement-packet/v1 and does not generate new measurement claims.",
            "Repair candidates are next inspection cues, not automatic fixes.",
            "Viewer scenes are visual projections, not structural verdict derivations."
        ]
    })
}

pub fn build_insight_brief_v1(report: &Value) -> String {
    let mut lines = Vec::new();
    lines.push("# ArchSig Insight Brief".to_string());
    lines.push(String::new());
    lines.push("## Read this first".to_string());
    lines.push(format!(
        "Conclusion: {}",
        string_at(report, &["readThisFirst", "conclusion"])
    ));
    lines.push(String::new());
    lines.push("What it means:".to_string());
    lines.push(string_at(report, &["readThisFirst", "whatItMeans"]));
    lines.push(String::new());
    lines.push("Where to look first:".to_string());
    for item in string_array_at(report, &["readThisFirst", "whereToLookFirst"])
        .into_iter()
        .take(5)
    {
        lines.push(format!("- {item}"));
    }
    lines.push(String::new());
    lines.push("Next action:".to_string());
    lines.push(string_at(report, &["readThisFirst", "nextAction"]));
    lines.push(String::new());
    lines.push("Boundary:".to_string());
    lines.push(string_at(report, &["readThisFirst", "boundary"]));
    lines.push(String::new());
    lines.push("## Top insights".to_string());
    for card in report["insightCards"]
        .as_array()
        .into_iter()
        .flatten()
        .take(3)
    {
        lines.push(format!(
            "- {}: {}",
            string_field(card, "title"),
            string_field(card, "oneLine")
        ));
        lines.push(format!(
            "  Why this matters: {}",
            string_field(card, "whyItMatters")
        ));
    }
    lines.push(String::new());
    lines.push("## Where to look".to_string());
    for block in report["copyBlocks"]["sourceRefs"]
        .as_array()
        .into_iter()
        .flatten()
        .take(10)
    {
        lines.push(format!("- {}", block.as_str().unwrap_or_default()));
    }
    lines.push(String::new());
    lines.push("## Suggested next inspections".to_string());
    for action in report["actionQueue"]
        .as_array()
        .into_iter()
        .flatten()
        .take(8)
    {
        lines.push(format!(
            "- {}: {}",
            string_field(action, "title"),
            string_field(action, "reason")
        ));
    }
    lines.push(String::new());
    lines.push("## Repair candidates".to_string());
    for card in report["insightCards"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|card| string_field(card, "kind") == "minimal_repair_candidate")
    {
        lines.push(format!("- {}", string_field(card, "oneLine")));
        lines.push("  Boundary: This is a combinatorial repair candidate, not a semantic refactor guarantee.".to_string());
    }
    if !lines
        .last()
        .is_some_and(|line| line.starts_with("  Boundary"))
    {
        lines.push("- No measured repair candidate was promoted by this packet.".to_string());
    }
    lines.push(String::new());
    lines.push("## Measurement boundary".to_string());
    lines.push(string_at(report, &["boundaryDigest", "shortText"]));
    lines.push(format!(
        "- checked: {}",
        number_at(report, &["boundaryDigest", "checkedCount"])
    ));
    lines.push(format!(
        "- assumed: {}",
        number_at(report, &["boundaryDigest", "assumedCount"])
    ));
    lines.push(format!(
        "- blocking: {}",
        number_at(report, &["boundaryDigest", "blockingCount"])
    ));
    if report["omittedDetailCounts"].is_object() {
        lines.push("- omitted detail counts:".to_string());
        for key in [
            "omittedAtoms",
            "omittedEdges",
            "omittedContextMemberships",
            "omittedCoverOverlaps",
            "omittedSceneLayerObjects",
            "omittedLabels",
            "omittedSourceRefs",
        ] {
            lines.push(format!(
                "  - {key}: {}",
                number_at(report, &["omittedDetailCounts", key])
            ));
        }
    }
    lines.push(String::new());
    lines.push("## Artifact links".to_string());
    for key in ["summaryRef", "briefRef", "viewerDataRef"] {
        lines.push(format!(
            "- {}: {}",
            key,
            string_at(report, &["outputArtifacts", key])
        ));
    }
    lines.push(String::new());
    lines.push("## Raw technical details".to_string());
    lines.push(format!(
        "- source packet: {}",
        string_field(report, "sourcePacketRef")
    ));
    lines.push(
        "- theorem-candidate readings are analytic-only and are not structural conclusions."
            .to_string(),
    );
    lines.push("- holonomy-like visual modes are exploratory cover / restriction path views, not monodromy verdicts.".to_string());
    lines.push(String::new());
    lines.push("## LLM handoff".to_string());
    lines.push("Use the following ArchSig result as bounded evidence.".to_string());
    lines.push("Do not infer beyond the listed claims and boundaries.".to_string());
    lines.push(String::new());
    lines.push("Conclusion:".to_string());
    lines.push(string_at(report, &["readThisFirst", "conclusion"]));
    lines.push(String::new());
    lines.push("Top insights:".to_string());
    for card in report["insightCards"]
        .as_array()
        .into_iter()
        .flatten()
        .take(3)
    {
        lines.push(format!("- {}", string_field(card, "oneLine")));
    }
    lines.push(String::new());
    lines.push("Boundary:".to_string());
    lines.push(string_at(report, &["boundaryDigest", "shortText"]));
    lines.push(String::new());
    lines.push("Source refs:".to_string());
    for source_ref in string_array_at(report, &["copyBlocks", "sourceRefs"])
        .into_iter()
        .take(10)
    {
        lines.push(format!("- {source_ref}"));
    }
    lines.push(String::new());
    lines.join("\n")
}

fn insight_cards_v1(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    summary: &Value,
) -> Vec<Value> {
    let mut cards = Vec::new();
    for row in &packet.structural_verdict {
        if row.evaluator == "ag.cech-obstruction@1" && row.verdict == "measured_nonzero" {
            cards.push(insight_card(
                "insight:h1-glue-mismatch:001",
                "global_glue_mismatch",
                "high",
                "Global glue mismatch measured",
                "Local checks do not explain the whole selected cover; ArchSig measured a cross-context H^1 mismatch.",
                "This highlights architecture drift that can be invisible as a local law violation and gives reviewers a first seam to inspect.",
                row,
                packet,
                normalized,
                "Inspect mismatch support",
                "cech-h1-mismatch",
                vec![
                    "measured_nonzero structural verdict".to_string(),
                    "has context refs".to_string(),
                    "has next inspection action".to_string(),
                ],
                vec![
                    "This does not prove source extraction completeness.".to_string(),
                    "This does not automatically identify a safe repair.".to_string(),
                ],
            ));
        } else if row.evaluator == "ag.cech-obstruction@1" && row.verdict == "measured_zero" {
            cards.push(insight_card(
                "insight:h1-glue-mismatch:zero",
                "no_measured_glue_mismatch",
                "info",
                "No measured H^1 glue mismatch under profile",
                "No selected-cover H^1 glue mismatch was measured under this profile.",
                "This lets reviewers distinguish a profile-relative zero result from unmeasured or unknown regions.",
                row,
                packet,
                normalized,
                "Inspect measurement boundary",
                "boundary-assumption",
                vec![
                    "measured_zero confirmation".to_string(),
                    "boundary digest remains visible".to_string(),
                ],
                vec![
                    "This does not mean the architecture is clean.".to_string(),
                    "This does not rule out unmeasured or unknown support.".to_string(),
                ],
            ));
        } else if row.evaluator == "ag.square-free-repair@1" && row.verdict == "measured_nonzero" {
            cards.push(insight_card(
                "insight:repair-candidate:001",
                "minimal_repair_candidate",
                "high",
                "Minimal repair candidate available",
                "Measured forbidden supports have a combinatorial hitting-set repair candidate.",
                "This gives refactor planning a concrete support set to inspect without claiming an automatic semantic repair.",
                row,
                packet,
                normalized,
                "Compare repair candidate with forbidden supports",
                "repair-dual",
                vec![
                    "repair candidate".to_string(),
                    "lower-bound language".to_string(),
                    "non-claim required".to_string(),
                ],
                vec![
                    "This is a combinatorial repair candidate, not a semantic refactor guarantee.".to_string(),
                    "This does not prove repair safety.".to_string(),
                ],
            ));
        } else if row.evaluator == "ag.law-conflict-tor@1" && row.verdict == "measured_nonzero" {
            cards.push(insight_card(
                "insight:policy-conflict:001",
                "policy_conflict",
                "high",
                "Policy conflict measured",
                "Selected law universes have a measured Tor conflict class in the common ambient.",
                "This points reviewers to the witness/context where policy choices structurally collide.",
                row,
                packet,
                normalized,
                "Inspect policy conflict witness",
                "law-conflict-tor",
                vec!["policy conflict".to_string(), "measured_nonzero structural verdict".to_string()],
                vec!["This does not prove there is no compatible refactor.".to_string()],
            ));
        } else if row.verdict == "not_computed" {
            cards.push(insight_card(
                &format!("insight:not-computed:{}", slug(&row.evaluator)),
                "not_computed_blocker",
                "high",
                "Measurement blocked by reason code",
                &format!(
                    "{} did not compute because {}.",
                    row.evaluator, row.verdict_data.method_status
                ),
                "The blocked reason belongs in the Decision Bar so reviewers do not mistake an empty scene for absence of conflict.",
                row,
                packet,
                normalized,
                "Inspect blocking reason",
                if row.evaluator == "ag.law-conflict-tor@1" {
                    "law-conflict-tor"
                } else {
                    "boundary-assumption"
                },
                vec![
                    "not_computed due to reason code".to_string(),
                    row.verdict_data.method_status.clone(),
                ],
                vec!["This is not a measured zero result.".to_string()],
            ));
        }
    }
    if packet
        .analytic_readings
        .iter()
        .any(|reading| reading.evaluator == "ag.sheaf-laplacian@1")
    {
        cards.push(analytic_insight_card(
            "insight:architecture-debt-mass:001",
            "architecture_debt_mass",
            "medium",
            "Architecture debt field available",
            "Harmonic mass and flatness distance are available as analytic readings.",
            "This supports debt inspection as an analytic field while keeping lawful/unlawful verdicts separate.",
            packet,
            normalized,
            "Inspect Hodge debt field",
            "hodge-debt-field",
            vec!["architecture debt mass / analytic reading".to_string()],
            vec![
                "Near-flat is not lawful.".to_string(),
                "Analytic readings do not generate structural verdicts.".to_string(),
            ],
        ));
    }
    if packet
        .assumptions
        .iter()
        .any(|assumption| assumption.status != "checked")
        || summary["structuralVerdictSummary"]["nonTerminalCount"]
            .as_u64()
            .unwrap_or(0)
            > 0
    {
        cards.push(analytic_insight_card(
            "insight:measurement-boundary:001",
            "measurement_boundary",
            "medium",
            "Measurement boundary recorded",
            "Checked, assumed, unmeasured, unknown, and not_computed states are preserved for review.",
            "This tells reviewers exactly where the conclusion is profile-relative and where it is blocked or unmeasured.",
            packet,
            normalized,
            "Inspect measurement boundary",
            "boundary-assumption",
            vec!["measurement boundary".to_string(), "unknown states remain visible".to_string()],
            vec!["Boundary visibility is not a negative conclusion by itself.".to_string()],
        ));
    }
    cards.sort_by(|left, right| {
        insight_rank(right)
            .cmp(&insight_rank(left))
            .then_with(|| string_field(left, "id").cmp(&string_field(right, "id")))
    });
    cards
}

fn insight_card(
    id: &str,
    kind: &str,
    severity: &str,
    title: &str,
    one_line: &str,
    why_it_matters: &str,
    row: &AgStructuralVerdictV1,
    packet: &ArchSigMeasurementPacketV1,
    normalized: &NormalizedArchMapV2,
    next_action: &str,
    scene_id: &str,
    ranking_basis: Vec<String>,
    non_claims: Vec<String>,
) -> Value {
    let refs = insight_refs_for_row(normalized, packet, row);
    let structural_verdict_ref = structural_verdict_ref(row);
    let sample_refs = insight_sample_refs(normalized);
    let evidence_resolution_status = if refs.3.is_empty() && refs.4.is_empty() && refs.5.is_empty()
    {
        "boundary_only"
    } else {
        "resolved_from_packet_support"
    };
    json!({
        "id": id,
        "kind": kind,
        "severity": severity,
        "title": title,
        "oneLine": one_line,
        "whyItMatters": why_it_matters,
        "evidence": {
            "structuralVerdictRefs": [structural_verdict_ref],
            "computedInvariantRefs": refs.0,
            "analyticReadingRefs": refs.1,
            "assumptionRefs": refs.2,
            "sourceRefs": refs.3,
            "atomRefs": refs.4,
            "contextRefs": refs.5,
            "coverRefs": [packet.profile.cover_ref.clone()],
            "evaluatorRefs": [row.evaluator.clone()],
            "evidenceResolutionStatus": evidence_resolution_status
        },
        "sampleRefs": sample_refs,
        "nextAction": {
            "label": next_action,
            "kind": if kind == "minimal_repair_candidate" { "repair_candidate" } else { "next_inspection" },
            "targetRefs": refs.6
        },
        "viewerNavigation": {
            "sceneId": scene_id,
            "highlightRefs": {
                "atomRefs": refs.4,
                "contextRefs": refs.5,
                "sourceRefs": refs.3
            }
        },
        "tourRefs": [format!("tour:{}", id.trim_start_matches("insight:"))],
        "rankingBasis": ranking_basis,
        "nonClaims": non_claims
    })
}

fn analytic_insight_card(
    id: &str,
    kind: &str,
    severity: &str,
    title: &str,
    one_line: &str,
    why_it_matters: &str,
    packet: &ArchSigMeasurementPacketV1,
    normalized: &NormalizedArchMapV2,
    next_action: &str,
    scene_id: &str,
    ranking_basis: Vec<String>,
    non_claims: Vec<String>,
) -> Value {
    let source_refs = top_source_refs(normalized);
    let atom_refs = top_atom_refs(normalized);
    let context_refs = top_context_refs(normalized);
    let sample_refs = insight_sample_refs(normalized);
    json!({
        "id": id,
        "kind": kind,
        "severity": severity,
        "title": title,
        "oneLine": one_line,
        "whyItMatters": why_it_matters,
        "evidence": {
            "structuralVerdictRefs": [],
            "computedInvariantRefs": invariant_refs(packet),
            "analyticReadingRefs": analytic_reading_refs(packet),
            "assumptionRefs": assumption_refs(packet),
            "sourceRefs": source_refs,
            "atomRefs": atom_refs,
            "contextRefs": context_refs,
            "coverRefs": [packet.profile.cover_ref.clone()],
            "evaluatorRefs": evaluator_refs(packet),
            "evidenceResolutionStatus": "analytic_or_boundary_summary"
        },
        "sampleRefs": sample_refs,
        "nextAction": {
            "label": next_action,
            "kind": "next_inspection",
            "targetRefs": ["boundary-digest:main"]
        },
        "viewerNavigation": {
            "sceneId": scene_id,
            "highlightRefs": {
                "atomRefs": atom_refs,
                "contextRefs": context_refs,
                "sourceRefs": source_refs
            }
        },
        "tourRefs": [format!("tour:{}", id.trim_start_matches("insight:"))],
        "rankingBasis": ranking_basis,
        "nonClaims": non_claims
    })
}

fn insight_boundary_digest(packet: &ArchSigMeasurementPacketV1, summary: &Value) -> Value {
    let checked = packet
        .assumptions
        .iter()
        .filter(|assumption| assumption.status == "checked")
        .count();
    let assumed = packet
        .assumptions
        .iter()
        .filter(|assumption| assumption.status == "assumed")
        .count();
    let violated = packet
        .assumptions
        .iter()
        .filter(|assumption| assumption.status == "violated")
        .count();
    let unmeasured = packet
        .structural_verdict
        .iter()
        .filter(|row| row.verdict == "unmeasured")
        .count();
    let unknown = packet
        .structural_verdict
        .iter()
        .filter(|row| row.verdict == "unknown")
        .count();
    let not_computed = packet
        .structural_verdict
        .iter()
        .filter(|row| row.verdict == "not_computed")
        .count();
    let blocking = violated + not_computed;
    json!({
        "id": "boundary-digest:main",
        "shortText": format!(
            "Profile-relative. {assumed} assumptions declared. {unmeasured} supports unmeasured. {unknown} unknown. {not_computed} not_computed."
        ),
        "profileRef": packet.profile.profile_id,
        "checkedCount": checked,
        "assumedCount": assumed,
        "violatedCount": violated,
        "unmeasuredCount": unmeasured,
        "unknownCount": unknown,
        "notComputedCount": not_computed,
        "blockingCount": blocking,
        "conclusionRef": summary["conclusion"],
        "checked": packet.assumptions.iter().filter(|row| row.status == "checked").map(assumption_row).collect::<Vec<_>>(),
        "assumed": packet.assumptions.iter().filter(|row| row.status == "assumed").map(assumption_row).collect::<Vec<_>>(),
        "blocking": packet.assumptions.iter().filter(|row| row.status == "violated").map(assumption_row).chain(packet.structural_verdict.iter().filter(|row| row.verdict == "not_computed").map(|row| json!({
            "kind": "not_computed",
            "evaluator": row.evaluator,
            "reasonCode": row.verdict_data.method_status,
            "reason": row.reason
        }))).collect::<Vec<_>>(),
        "nonClaims": [
            "Boundary digest qualifies where the conclusion applies; it does not add a new negative conclusion.",
            "Unmeasured, unknown, and not_computed are not measured zero."
        ]
    })
}

fn insight_omitted_detail_counts_v1(normalized: &NormalizedArchMapV2, scenes: &[Value]) -> Value {
    let atom_count = normalized.atoms.len();
    let context_memberships = normalized
        .atoms
        .iter()
        .map(|atom| atom.context_memberships.len())
        .sum::<usize>();
    let cover_overlaps = normalized
        .covers
        .iter()
        .map(|cover| cover.context_ids.len().saturating_sub(1))
        .sum::<usize>();
    let scene_layer_objects = scenes
        .iter()
        .flat_map(|scene| scene["layers"].as_array().into_iter().flatten())
        .count();
    json!({
        "omittedAtoms": if atom_count > 10_000 { atom_count.saturating_sub(10_000) } else { 0 },
        "omittedEdges": 0,
        "omittedContextMemberships": if context_memberships > 20_000 { context_memberships.saturating_sub(20_000) } else { 0 },
        "omittedCoverOverlaps": if cover_overlaps > 10_000 { cover_overlaps.saturating_sub(10_000) } else { 0 },
        "omittedSceneLayerObjects": if scene_layer_objects > 1_000 { scene_layer_objects.saturating_sub(1_000) } else { 0 },
        "omittedLabels": if atom_count > 10_000 { atom_count.saturating_sub(10_000) } else { 0 },
        "omittedSourceRefs": 0,
        "omittedReasons": [
            "large graph projection may aggregate background geometry",
            "top insight support and blocking reason objects are preserved before background objects",
            "viewer data remains a projection and does not embed raw source content"
        ]
    })
}

fn insight_action_queue_v1(cards: &[Value]) -> Vec<Value> {
    cards
        .iter()
        .enumerate()
        .map(|(index, card)| {
            let kind = if string_field(card, "kind") == "minimal_repair_candidate" {
                "repair_candidate"
            } else {
                "next_inspection"
            };
            json!({
                "id": format!("action:{}:{}", kind, index + 1),
                "kind": kind,
                "title": string_at(card, &["nextAction", "label"]),
                "reason": string_field(card, "oneLine"),
                "targetRefs": card["nextAction"]["targetRefs"],
                "expectedUserOutcome": if kind == "repair_candidate" {
                    "Decide whether this combinatorial candidate should seed a refactor plan."
                } else {
                    "Decide which measured support, boundary, or source ref to inspect next."
                },
                "nonClaims": card["nonClaims"]
            })
        })
        .collect()
}

fn insight_viewer_visual_scenes_v1(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    cards: &[Value],
    gluing_geometry: &Value,
) -> Vec<Value> {
    let overview_refs = scene_refs_for_kinds(
        normalized,
        packet,
        cards,
        &[
            "global_glue_mismatch",
            "minimal_repair_candidate",
            "policy_conflict",
            "not_computed_blocker",
            "architecture_debt_mass",
            "measurement_boundary",
            "confirmed_zero",
            "no_measured_glue_mismatch",
        ],
        true,
    );
    let cech_refs = scene_refs_for_kinds(
        normalized,
        packet,
        cards,
        &[
            "global_glue_mismatch",
            "confirmed_zero",
            "no_measured_glue_mismatch",
        ],
        false,
    );
    let obstruction_refs = scene_refs_for_kinds(
        normalized,
        packet,
        cards,
        &["minimal_repair_candidate"],
        false,
    );
    let law_refs = scene_refs_for_kinds(
        normalized,
        packet,
        cards,
        &["policy_conflict", "not_computed_blocker"],
        false,
    );
    let hodge_refs = scene_refs_for_kinds(
        normalized,
        packet,
        cards,
        &["architecture_debt_mass"],
        false,
    );
    let boundary_refs =
        scene_refs_for_kinds(normalized, packet, cards, &["measurement_boundary"], false);
    let source_refs = source_scene_refs(normalized, packet, cards);
    let has_glue_mismatch = cards
        .iter()
        .any(|card| string_field(card, "kind") == "global_glue_mismatch");
    let has_glue_zero = cards.iter().any(|card| {
        matches!(
            string_field(card, "kind").as_str(),
            "confirmed_zero" | "no_measured_glue_mismatch"
        )
    });
    let has_repair = cards
        .iter()
        .any(|card| string_field(card, "kind") == "minimal_repair_candidate");
    let has_policy_conflict = cards
        .iter()
        .any(|card| string_field(card, "kind") == "policy_conflict");
    let has_not_computed_blocker = cards
        .iter()
        .any(|card| string_field(card, "kind") == "not_computed_blocker");
    let has_debt = cards
        .iter()
        .any(|card| string_field(card, "kind") == "architecture_debt_mass");
    let scenes = vec![
        scene_v1(
            "overview",
            "overview_constellation",
            "Overview",
            "Which insight should I inspect first?",
            (
                "source locality / module neighborhood",
                "architecture layer or atom family rank",
                "insight priority / measured severity",
            ),
            "top_insight_beacon",
            "beacon",
            "topInsightBeacon",
            "selected insight support",
            &overview_refs,
            overview_color_role(cards),
            "sphere",
            "thick_glowing_line",
            true,
        ),
        scene_v1(
            "site-cover",
            "finite_poset_site",
            "Site / Cover",
            "What finite site and cover did ArchSig measure?",
            (
                "source neighborhood",
                "poset rank",
                "coverage density or context size",
            ),
            "context_patch",
            "patch",
            "contextPatch",
            "context and cover membership",
            &overview_refs,
            "checked",
            "translucent_patch",
            "arrow",
            true,
        ),
        scene_v1(
            "cech-gluing",
            "cover_gluing",
            "Cover & Gluing",
            "Where does local structure fail to glue globally?",
            (
                "context neighborhood / source locality",
                "context rank / restriction depth",
                "gluing mismatch intensity",
            ),
            "overlap_seam",
            "ribbon",
            "cechMismatchSeam",
            "overlap seam and gluing mismatch",
            &cech_refs,
            if has_glue_mismatch {
                "measured_nonzero"
            } else {
                "measured_zero"
            },
            "ribbon",
            "thick_glowing_line",
            has_glue_mismatch || has_glue_zero,
        ),
        scene_v1(
            "cech-h1-mismatch",
            "cech_h1_mismatch",
            "H1 Mismatch",
            "Which mismatch class remains after local explanations?",
            (
                "cover overlap support",
                "cochain / coboundary role",
                "H1 mismatch weight",
            ),
            "cocycle_ribbon",
            "ribbon",
            "cechMismatchSeam",
            "cocycle representative support",
            &cech_refs,
            if has_glue_mismatch {
                "measured_nonzero"
            } else {
                "measured_zero"
            },
            "ribbon",
            "thick_glowing_line",
            has_glue_mismatch || has_glue_zero,
        ),
        scene_v1(
            "obstruction",
            "forbidden_support",
            "Obstruction",
            "Which atom combinations form forbidden support?",
            (
                "atom support neighborhood",
                "law family",
                "obstruction intensity",
            ),
            "forbidden_support_cage",
            "cage",
            "forbiddenSupportCage",
            "minimal forbidden support",
            &obstruction_refs,
            "measured_nonzero",
            "cage",
            "broken_line",
            has_repair,
        ),
        with_scene_non_claims(
            scene_v1(
                "repair-dual",
                "repair_dual",
                "Repair",
                "Which candidate support intersects measured obstructions?",
                ("forbidden support", "candidate set", "lower-bound pressure"),
                "repair_candidate_cut",
                "cut",
                "repairCandidateCut",
                "minimal repair hitting set; not automatic repair",
                &obstruction_refs,
                "repair_candidate",
                "cut",
                "arrow",
                has_repair,
            ),
            &[
                "This is a combinatorial repair candidate. It is not a semantic refactor guarantee.",
                "This does not prove repair safety.",
            ],
        ),
        scene_v1(
            "law-conflict-tor",
            "law_conflict",
            "Law Conflict",
            "Which law universe conflict is loaded on which witness?",
            (
                "law universe A",
                "common ambient / blocker",
                "law universe B",
            ),
            "law_conflict_bridge",
            "bridge",
            "lawConflictBridge",
            if has_not_computed_blocker {
                "no_common_ambient blocker or not_computed reason code"
            } else {
                "common ambient conflict witness"
            },
            &law_refs,
            if has_not_computed_blocker {
                "not_computed"
            } else if has_policy_conflict {
                "measured_nonzero"
            } else {
                "not_applicable"
            },
            "wall",
            "broken_line",
            has_policy_conflict || has_not_computed_blocker,
        ),
        scene_v1(
            "hodge-debt-field",
            "hodge_debt_field",
            "Hodge Debt Field",
            "Where is analytic architecture debt mass concentrated?",
            (
                "support locality",
                "harmonic / exact component",
                "debt mass / flatness distance",
            ),
            "analytic_debt_field",
            "field",
            "hodgeDebtField",
            "harmonic mass analytic reading",
            &hodge_refs,
            "analytic_reading",
            "heat",
            "contour",
            has_debt,
        ),
        boundary_scene_v1(&boundary_refs),
        scene_v1(
            "source-evidence",
            "source_evidence",
            "Source Evidence",
            "Which source refs ground this insight?",
            (
                "path / directory neighborhood",
                "symbol / file depth",
                "evidence role",
            ),
            "source_node",
            "node",
            "sourceNode",
            "copyable source refs",
            &source_refs,
            "source_evidence",
            "node",
            "thin_line",
            !string_array_at(&source_refs, &["sourceRefs"]).is_empty(),
        ),
    ];
    scenes
        .into_iter()
        .map(|scene| attach_gluing_scene_geometry(scene, gluing_geometry))
        .collect()
}

fn attach_gluing_scene_geometry(mut scene: Value, gluing_geometry: &Value) -> Value {
    let scene_id = string_field(&scene, "sceneId");
    let geometry_refs = match scene_id.as_str() {
        "site-cover" | "cech-gluing" => json!({
            "nerveRef": "gluingGeometry.nerve",
            "projectionObjectKinds": ["nerveVertex", "nerveEdge", "nerveTriangle"]
        }),
        "cech-h1-mismatch" => json!({
            "cocycleRibbonRef": "gluingGeometry.cocycleRibbon",
            "projectionObjectKinds": ["cocycleRibbon", "holonomyLikeGapMarker"]
        }),
        "obstruction" => json!({
            "forbiddenCagesRef": "gluingGeometry.forbiddenCages",
            "projectionObjectKinds": ["forbiddenSupportCage", "simplexEdge"]
        }),
        "repair-dual" => json!({
            "repairMorphsRef": "gluingGeometry.repairMorphs",
            "projectionObjectKinds": ["repairMorphPath", "lowerBoundMarker"]
        }),
        "hodge-debt-field" => json!({
            "locusFieldRef": "gluingGeometry.locusField",
            "projectionObjectKinds": ["curvatureHeightField", "blockedUnmeasuredRegion"]
        }),
        _ => json!({
            "projectionObjectKinds": []
        }),
    };
    scene["gluingGeometryRefs"] = geometry_refs;
    scene["axisMappingImplemented"] = json!(true);
    scene["axisMetricBindings"] = json!({
        "x": "xValue",
        "y": "yValue",
        "z": "zValue",
        "fallbackBlend": 0.35,
        "source": "renderer sceneAxisPosition reads these metric keys from each gluing geometry object"
    });
    scene["projectionBoundary"] = json!(
        "Scene geometry is a bounded projection of archsig-measurement-packet/v1 and archsig-insight-report/v1; it does not create a new structural verdict."
    );
    scene["visualEncodingLegend"] = visual_encoding_legend_v1();
    if scene_id == "cech-h1-mismatch" {
        let mut non_claims = string_array_at(&scene, &["nonClaims"]);
        non_claims.push(
            "Holonomy-like ribbon closure is an exploratory restriction-path view, not a monodromy verdict."
                .to_string(),
        );
        scene["nonClaims"] = json!(non_claims);
    }
    if scene_id == "repair-dual" {
        let mut non_claims = string_array_at(&scene, &["nonClaims"]);
        non_claims.push(
            "Repair morph animation shows lower-bound movement only; it is not an automatic repair."
                .to_string(),
        );
        scene["nonClaims"] = json!(non_claims);
    }
    if scene_id == "hodge-debt-field"
        && gluing_geometry["locusField"]["blockedRegions"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    {
        scene["visualEncodings"][0]["textRole"] = json!(
            "curvature support field; blocked/unmeasured remains visibly separate from measured-zero"
        );
    }
    scene
}

fn visual_encoding_legend_v1() -> Value {
    json!([
        {
            "channel": "color",
            "meaning": "measurement state",
            "values": {
                "measured_nonzero": "amber obstruction or mismatch support",
                "measured_zero": "teal selected-support zero",
                "not_computed": "red blocker",
                "unmeasured": "gray unmeasured region",
                "repair_candidate": "violet lower-bound repair candidate"
            }
        },
        {
            "channel": "shape",
            "meaning": "geometry object kind",
            "values": {
                "triangle": "packet cover triple simplex face",
                "ribbon": "Cech support path with closure gap marker",
                "cage": "minimal forbidden support simplex",
                "morph": "repair candidate lower-bound path",
                "glyph": "atom fiber/carrier/valence/semantic-anchor encoding"
            }
        },
        {
            "channel": "line",
            "meaning": "claim boundary",
            "values": {
                "solid": "measured or checked relation",
                "dashed": "blocked/unmeasured boundary",
                "thick": "top insight support"
            }
        },
        {
            "channel": "opacity",
            "meaning": "projection confidence",
            "values": {
                "opaque": "source-backed selected support",
                "translucent": "context or omitted background projection"
            }
        },
        {
            "channel": "thickness",
            "meaning": "support priority",
            "values": {
                "thick": "top insight or nonzero support",
                "thin": "orientation or background relation"
            }
        }
    ])
}

fn gluing_geometry_projection_v1(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
) -> Value {
    let selected_contexts = selected_cover_contexts(normalized, &packet.profile);
    let cech_edges = cech_edges(normalized, &selected_contexts);
    let cover_nerve_projection = packet
        .computed_invariants
        .iter()
        .find_map(|invariant| invariant.get("coverNerveProjection").cloned())
        .unwrap_or_else(|| {
            empty_cover_nerve_projection_v1(
                &packet.profile.cover_ref,
                "missing packet coverNerveProjection; viewer does not infer cover triangles",
            )
        });
    let cover = normalized.covers.iter().find(|cover| {
        cover.normalized_cover_id == packet.profile.cover_ref
            || cover.source_cover_id == packet.profile.cover_ref
    });
    let cover_refs = cover
        .map(|cover| cover.source_refs.clone())
        .unwrap_or_default();
    let nonzero_edges = cech_edges
        .iter()
        .filter(|edge| edge.value > 0 || !edge.support_atom_refs.is_empty())
        .collect::<Vec<_>>();
    let class_nonzero = packet
        .computed_invariants
        .iter()
        .find_map(|invariant| {
            invariant
                .get("observedCocycle")
                .and_then(|cocycle| cocycle.get("classNonzero"))
                .and_then(Value::as_bool)
        })
        .unwrap_or(false);
    let cocycle_support_atom_refs = nonzero_edges
        .iter()
        .flat_map(|edge| edge.support_atom_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let forbidden_cages = forbidden_cage_projection(normalized, packet);
    let repair_morphs = repair_morph_projection(normalized, packet, &forbidden_cages);
    let locus_field = locus_field_projection(packet);
    let atom_glyphs = atom_glyph_projection(normalized);
    let triangle_count = cover_nerve_projection["faces"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let field_row_count = locus_field["fieldRows"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let blocked_region_count = locus_field["blockedRegions"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let zero_region_count = locus_field["measuredZeroRegions"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let atom_glyph_total_count = normalized.atoms.len();
    json!({
        "schema": "archsig-viewer-gluing-geometry/v1",
        "sourcePacketRef": "archsig-measurement-packet.json",
        "sourceInsightReportRef": "archsig-insight-report.json",
        "projectionBoundary": "This geometry translates measured packet and ArchMap cover support into viewer objects. It adds no structural verdict, H2 coherence claim, or monodromy verdict.",
        "nerve": {
            "coverRef": packet.profile.cover_ref,
            "sourceRefs": cover_refs,
            "vertices": cover_nerve_projection["vertices"],
            "edges": cover_nerve_projection["edges"],
            "triangles": cover_nerve_projection["faces"],
            "triangleSource": cover_nerve_projection["faceSource"],
            "h2CoherenceVisualized": cover_nerve_projection["h2CoherenceVisualized"]
        },
        "cocycleRibbon": {
            "supportAtomRefs": cocycle_support_atom_refs,
            "supportEdges": nonzero_edges.iter().map(|edge| json!({
                "edgeId": edge.edge_id,
                "sourceContextRef": edge.source_context,
                "targetContextRef": edge.target_context,
                "value": edge.value,
                "supportAtomRefs": edge.support_atom_refs
            })).collect::<Vec<_>>(),
            "closureGapEncoding": {
                "kind": "holonomyLikeGapMarker",
                "visible": class_nonzero && !nonzero_edges.is_empty(),
                "lineRole": "thick_glowing_dashed_seam",
                "source": "observedCocycle.classNonzero plus representative support from packet",
                "nonClaim": "Exploratory restriction-path closure gap only; monodromy verdict is not generated."
            }
        },
        "locusField": locus_field,
        "forbiddenCages": forbidden_cages,
        "repairMorphs": repair_morphs,
        "atomGlyphs": atom_glyphs,
        "visualEncodingLegend": visual_encoding_legend_v1(),
        "renderLimits": {
            "nerveTriangles": GLUING_TRIANGLE_RENDER_LIMIT,
            "curvatureFieldRows": GLUING_FIELD_ROW_RENDER_LIMIT,
            "curvatureRegions": GLUING_REGION_RENDER_LIMIT,
            "forbiddenCages": GLUING_CAGE_RENDER_LIMIT,
            "repairMorphs": GLUING_MORPH_RENDER_LIMIT,
            "atomGlyphs": GLUING_ATOM_GLYPH_RENDER_LIMIT
        },
        "omittedGeometryCounts": {
            "nerveTriangles": triangle_count.saturating_sub(GLUING_TRIANGLE_RENDER_LIMIT),
            "cocycleSupportEdges": 0,
            "curvatureFieldRows": field_row_count.saturating_sub(GLUING_FIELD_ROW_RENDER_LIMIT),
            "measuredZeroRegions": zero_region_count.saturating_sub(GLUING_REGION_RENDER_LIMIT),
            "blockedRegions": blocked_region_count.saturating_sub(GLUING_REGION_RENDER_LIMIT),
            "forbiddenCages": forbidden_cages.len().saturating_sub(GLUING_CAGE_RENDER_LIMIT),
            "repairMorphs": repair_morphs.len().saturating_sub(GLUING_MORPH_RENDER_LIMIT),
            "atomGlyphs": atom_glyph_total_count.saturating_sub(GLUING_ATOM_GLYPH_RENDER_LIMIT)
        },
        "nonClaims": [
            "No H2 coherence failure is visualized by this projection.",
            "Holonomy-like ribbon display is not a monodromy verdict.",
            "Repair morphs are lower-bound inspection aids, not automatic repairs."
        ]
    })
}

fn context_atom_refs(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &[String],
) -> BTreeMap<String, Vec<String>> {
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    normalized
        .contexts
        .iter()
        .filter(|context| selected.contains(&context.normalized_context_id))
        .map(|context| {
            (
                context.normalized_context_id.clone(),
                context.atom_ids.iter().take(24).cloned().collect(),
            )
        })
        .collect()
}

fn forbidden_cage_projection(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
) -> Vec<Value> {
    let atom_refs_by_variable = atom_refs_by_square_free_variable(normalized);
    let mut cages = Vec::new();
    for invariant in &packet.computed_invariants {
        let generators = invariant["obstructionIdeal"]["generators"]
            .as_array()
            .into_iter()
            .flatten();
        for generator in generators {
            let support_atom_refs = string_array_at(generator, &["supportAtomRefs"]);
            let support_variables = string_array_at(generator, &["support"]);
            if support_atom_refs.is_empty() && support_variables.is_empty() {
                continue;
            }
            let atom_refs = if support_atom_refs.is_empty() {
                support_variables
                    .iter()
                    .filter_map(|variable| atom_refs_by_variable.get(variable))
                    .flatten()
                    .cloned()
                    .collect::<Vec<_>>()
            } else {
                support_atom_refs
            };
            let generator_id = string_field(generator, "generatorId");
            cages.push(json!({
                "cageId": format!("forbidden-cage:{generator_id}"),
                "atomRefs": atom_refs,
                "supportVariables": support_variables,
                "sourceInvariantRef": invariant["invariantId"],
                "sourceGeneratorRef": generator_id,
                "shapeRole": "cage",
                "lineRole": "broken_line",
                "source": "packet obstructionIdeal.generators[].supportAtomRefs/support"
            }));
        }
    }
    cages
}

fn repair_morph_projection(
    _normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    forbidden_cages: &[Value],
) -> Vec<Value> {
    let lower_bound_readings = packet
        .analytic_readings
        .iter()
        .filter(|reading| {
            reading.reading_id.contains("repair")
                || reading.evaluator.contains("support-transfer")
                || reading.value.to_string().contains("lower-bound")
        })
        .collect::<Vec<_>>();
    let repair_candidates = packet
        .computed_invariants
        .iter()
        .flat_map(|invariant| {
            invariant["alexanderDualRepair"]["minimalHittingSets"]
                .as_array()
                .into_iter()
                .flatten()
                .enumerate()
                .map(|(index, hitting_set)| {
                    json!({
                        "candidateId": format!("{}:repair-candidate:{index}", string_field(invariant, "invariantId")),
                        "sourceInvariantRef": invariant["invariantId"],
                        "supportVariables": hitting_set
                            .as_array()
                            .into_iter()
                            .flatten()
                            .filter_map(Value::as_str)
                            .map(ToOwned::to_owned)
                            .collect::<Vec<_>>()
                    })
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    repair_candidates
        .iter()
        .enumerate()
        .map(|(index, candidate)| {
            let candidate_variables = string_array_at(candidate, &["supportVariables"]);
            let related_cages = related_forbidden_cages(forbidden_cages, candidate);
            let from_cage_ref = related_cages
                .get(index % related_cages.len().max(1))
                .or_else(|| related_cages.first())
                .cloned()
                .unwrap_or_else(|| "forbidden-cage:unavailable".to_string());
            let from_atom_refs = related_cages
                .iter()
                .filter_map(|cage_id| {
                    forbidden_cages
                        .iter()
                        .find(|cage| cage["cageId"] == *cage_id)
                })
                .flat_map(|cage| string_array_at(cage, &["atomRefs"]))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            json!({
                "morphId": format!("repair-morph:{}", string_field(candidate, "candidateId")),
                "fromCageRef": from_cage_ref,
                "fromCageRefs": related_cages,
                "fromAtomRefs": from_atom_refs,
                "toCandidateRef": candidate["candidateId"],
                "supportVariables": candidate_variables,
                "sourceInvariantRef": candidate["sourceInvariantRef"],
                "lowerBoundReadingRefs": lower_bound_readings
                    .iter()
                    .map(|reading| reading.reading_id.clone())
                    .take(8)
                    .collect::<Vec<_>>(),
                "animationRole": "continuous_morph_lower_bound",
                "samplePhase": index,
                "nonClaim": "not automatic repair"
            })
        })
        .collect()
}

fn atom_refs_by_square_free_variable(
    normalized: &NormalizedArchMapV2,
) -> BTreeMap<String, Vec<String>> {
    let mut refs_by_variable = BTreeMap::<String, Vec<String>>::new();
    for atom in &normalized.atoms {
        for key in [
            atom.source_atom_id.as_str(),
            atom.normalized_atom_id.as_str(),
            atom.subject.as_str(),
        ] {
            refs_by_variable
                .entry(key.to_string())
                .or_default()
                .push(atom.normalized_atom_id.clone());
        }
    }
    refs_by_variable
}

fn related_forbidden_cages(forbidden_cages: &[Value], candidate: &Value) -> Vec<String> {
    let source_invariant = string_field(candidate, "sourceInvariantRef");
    let candidate_variables = string_array_at(candidate, &["supportVariables"])
        .into_iter()
        .collect::<BTreeSet<_>>();
    let mut related = forbidden_cages
        .iter()
        .filter(|cage| {
            cage["sourceInvariantRef"] == source_invariant
                && string_array_at(cage, &["supportVariables"])
                    .into_iter()
                    .any(|variable| candidate_variables.contains(&variable))
        })
        .filter_map(|cage| cage["cageId"].as_str().map(ToOwned::to_owned))
        .collect::<Vec<_>>();
    if related.is_empty() {
        related = forbidden_cages
            .iter()
            .filter(|cage| cage["sourceInvariantRef"] == source_invariant)
            .filter_map(|cage| cage["cageId"].as_str().map(ToOwned::to_owned))
            .collect();
    }
    related
}

fn locus_field_projection(packet: &ArchSigMeasurementPacketV1) -> Value {
    let mut field_rows = packet
        .structural_verdict
        .iter()
        .enumerate()
        .filter(|(_, row)| row.evaluator.contains("curvature") || row.law.contains("curvature"))
        .map(|(index, row)| {
            json!({
                "fieldId": format!("curvature-field:{index}:{}", row.evaluator),
                "status": row.verdict,
                "height": if row.verdict == "measured_nonzero" { 1 } else { 0 },
                "colorRole": match row.verdict.as_str() {
                    "measured_nonzero" => "measured_nonzero",
                    "measured_zero" => "measured_zero",
                    "not_computed" => "not_computed",
                    "unmeasured" => "unmeasured",
                    _ => "unknown"
                },
                "source": "structural verdict curvature row"
            })
        })
        .collect::<Vec<_>>();
    field_rows.extend(analytic_locus_field_rows(packet));
    let blocked_regions = packet
        .structural_verdict
        .iter()
        .filter(|row| {
            matches!(
                row.verdict.as_str(),
                "unmeasured" | "unknown" | "not_computed"
            )
        })
        .map(|row| {
            json!({
                "regionId": format!("blocked-region:{}", row.evaluator),
                "status": row.verdict,
                "shapeRole": "blocked_unmeasured_region",
                "source": "non-terminal packet verdict"
            })
        })
        .collect::<Vec<_>>();
    let measured_zero_regions = packet
        .structural_verdict
        .iter()
        .filter(|row| row.verdict == "measured_zero")
        .map(|row| {
            json!({
                "regionId": format!("measured-zero-region:{}", row.evaluator),
                "status": row.verdict,
                "shapeRole": "smooth_measured_zero_patch",
                "source": "selected-support zero packet verdict"
            })
        })
        .collect::<Vec<_>>();
    json!({
        "fieldRows": field_rows,
        "measuredZeroRegions": measured_zero_regions,
        "blockedRegions": blocked_regions
    })
}

fn analytic_locus_field_rows(packet: &ArchSigMeasurementPacketV1) -> Vec<Value> {
    let mut rows = Vec::new();
    for reading in &packet.analytic_readings {
        let reading_kind = string_at(&reading.value, &["readingKind"]);
        if reading_kind != "graph-laplacian-hodge-proxy@1" {
            continue;
        }
        let harmonic_mass = reading.value["harmonicMass"].as_f64().unwrap_or(0.0);
        let distance_to_flatness = reading.value["distanceToFlatness"].as_f64().unwrap_or(0.0);
        let mass_height = harmonic_mass.max(distance_to_flatness);
        rows.push(json!({
            "fieldId": format!("curvature-mass:{}", reading.reading_id),
            "status": "analytic_reading",
            "height": round_f64(mass_height),
            "harmonicMass": round_f64(harmonic_mass),
            "distanceToFlatness": round_f64(distance_to_flatness),
            "colorRole": "analytic_reading",
            "sourceReadingRef": reading.reading_id,
            "source": "analytic reading harmonicMass / distanceToFlatness"
        }));
        for (index, transfer) in reading.value["curvatureTransferSpectrum"]
            .as_array()
            .into_iter()
            .flatten()
            .enumerate()
        {
            let curvature = transfer["curvature"].as_f64().unwrap_or(0.0);
            rows.push(json!({
                "fieldId": format!("curvature-support:{}:{index}", reading.reading_id),
                "status": "analytic_reading",
                "height": round_f64(curvature.abs()),
                "signedCurvature": round_f64(curvature),
                "cellRef": string_field(transfer, "cell"),
                "harmonicMass": round_f64(harmonic_mass),
                "distanceToFlatness": round_f64(distance_to_flatness),
                "colorRole": if curvature.abs() > 1.0e-9 { "analytic_reading" } else { "measured_zero" },
                "sourceReadingRef": reading.reading_id,
                "source": "analytic reading curvatureTransferSpectrum support / mass"
            }));
        }
    }
    rows
}

fn atom_glyph_projection(normalized: &NormalizedArchMapV2) -> Vec<Value> {
    normalized
        .atoms
        .iter()
        .take(GLUING_ATOM_GLYPH_RENDER_LIMIT)
        .map(|atom| {
            let semantic_anchor_missing =
                atom.subject.is_empty() || atom.source_refs.is_empty() || atom.axis == "unknown";
            json!({
                "atomRef": atom.normalized_atom_id,
                "fiber": atom.atom_kind,
                "carrier": atom.subject,
                "valence": atom.context_memberships.len(),
                "semanticAnchor": if semantic_anchor_missing { "blocked_missing_anchor" } else { "source_backed" },
                "shapeRole": if semantic_anchor_missing { "blocked_anchor_glyph" } else { "structured_atom_glyph" },
                "fiberShapeRole": format!("fiber_shape:{}", atom.atom_kind),
                "carrierColorRole": format!("carrier_color:{}", slug(&atom.subject)),
                "sizeRole": "valence",
                "colorRole": if semantic_anchor_missing { "not_computed" } else { "source_evidence" }
            })
        })
        .collect()
}

fn overview_color_role(cards: &[Value]) -> &'static str {
    let top_kind = cards.first().map(|card| string_field(card, "kind"));
    match top_kind.as_deref() {
        Some("global_glue_mismatch")
        | Some("minimal_repair_candidate")
        | Some("policy_conflict") => "measured_nonzero",
        Some("no_measured_glue_mismatch") | Some("confirmed_zero") => "measured_zero",
        Some("not_computed_blocker") => "not_computed",
        Some("architecture_debt_mass") => "analytic_reading",
        Some("measurement_boundary") => "unknown",
        _ => "checked",
    }
}

fn scene_refs_for_kinds(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    cards: &[Value],
    kinds: &[&str],
    include_samples: bool,
) -> Value {
    let kind_set = kinds.iter().copied().collect::<BTreeSet<_>>();
    let mut insight_refs = Vec::new();
    let mut atom_refs = BTreeSet::new();
    let mut context_refs = BTreeSet::new();
    let mut source_refs = BTreeSet::new();

    for card in cards
        .iter()
        .filter(|card| kind_set.contains(string_field(card, "kind").as_str()))
    {
        insight_refs.push(string_field(card, "id"));
        for atom_ref in string_array_at(card, &["evidence", "atomRefs"]) {
            atom_refs.insert(atom_ref);
        }
        for context_ref in string_array_at(card, &["evidence", "contextRefs"]) {
            context_refs.insert(context_ref);
        }
        for source_ref in string_array_at(card, &["evidence", "sourceRefs"]) {
            source_refs.insert(source_ref);
        }
    }

    if include_samples {
        atom_refs.extend(top_atom_refs(normalized));
        context_refs.extend(top_context_refs(normalized));
        source_refs.extend(top_source_refs(normalized));
    }

    json!({
        "insightRefs": insight_refs,
        "atomRefs": atom_refs.into_iter().take(24).collect::<Vec<_>>(),
        "contextRefs": context_refs.into_iter().take(16).collect::<Vec<_>>(),
        "coverRefs": [packet.profile.cover_ref.clone()],
        "sourceRefs": source_refs.into_iter().take(20).collect::<Vec<_>>()
    })
}

fn source_scene_refs(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    cards: &[Value],
) -> Value {
    let mut insight_refs = Vec::new();
    let mut atom_refs = BTreeSet::new();
    let mut context_refs = BTreeSet::new();
    let mut source_refs = BTreeSet::new();
    for card in cards
        .iter()
        .filter(|card| !string_array_at(card, &["evidence", "sourceRefs"]).is_empty())
    {
        insight_refs.push(string_field(card, "id"));
        for atom_ref in string_array_at(card, &["evidence", "atomRefs"]) {
            atom_refs.insert(atom_ref);
        }
        for context_ref in string_array_at(card, &["evidence", "contextRefs"]) {
            context_refs.insert(context_ref);
        }
        for source_ref in string_array_at(card, &["evidence", "sourceRefs"]) {
            source_refs.insert(source_ref);
        }
    }
    if source_refs.is_empty() {
        source_refs.extend(top_source_refs(normalized));
    }
    json!({
        "insightRefs": insight_refs,
        "atomRefs": atom_refs.into_iter().take(24).collect::<Vec<_>>(),
        "contextRefs": context_refs.into_iter().take(16).collect::<Vec<_>>(),
        "coverRefs": [packet.profile.cover_ref.clone()],
        "sourceRefs": source_refs.into_iter().take(20).collect::<Vec<_>>()
    })
}

fn scene_v1(
    scene_id: &str,
    kind: &str,
    title: &str,
    user_question: &str,
    axis: (&str, &str, &str),
    layer_kind: &str,
    geometry_role: &str,
    click_target_kind: &str,
    text_role: &str,
    primary_refs: &Value,
    color_role: &str,
    shape_role: &str,
    line_role: &str,
    active: bool,
) -> Value {
    json!({
        "sceneId": scene_id,
        "kind": kind,
        "title": title,
        "sceneStatus": if active { "active" } else { "not_active_for_packet" },
        "userQuestion": user_question,
        "axisMapping": { "x": axis.0, "y": axis.1, "z": axis.2 },
        "primaryRefs": primary_refs,
        "layers": [{
            "layerId": format!("layer:{scene_id}:{layer_kind}"),
            "kind": layer_kind,
            "geometryRole": geometry_role,
            "encodingRef": format!("encoding:{scene_id}:main"),
            "clickTargetKind": click_target_kind,
            "refs": primary_refs,
            "omissionPolicy": if active { "preserve_for_top_insight" } else { "omittable_background" },
            "animationPurpose": if active { "navigation" } else { "orientation" }
        }],
        "visualEncodings": [{
            "encodingId": format!("encoding:{scene_id}:main"),
            "colorRole": if active { color_role } else { "not_applicable" },
            "shapeRole": shape_role,
            "lineRole": line_role,
            "textRole": if active { text_role.to_string() } else { format!("not active for this packet: {text_role}") }
        }],
        "boundaryDigestRef": "boundary-digest:main"
    })
}

fn with_scene_non_claims(mut scene: Value, non_claims: &[&str]) -> Value {
    scene["nonClaims"] = json!(non_claims);
    scene
}

fn boundary_scene_v1(primary_refs: &Value) -> Value {
    let states = [
        (
            "checked",
            "checked_boundary_surface",
            "surface",
            "boundaryChecked",
            "checked evidence boundary",
            "checked",
            "solid_surface",
            "thin_line",
        ),
        (
            "assumed",
            "assumed_boundary_surface",
            "surface",
            "boundaryAssumed",
            "assumed profile boundary",
            "assumed",
            "translucent_surface",
            "thin_line",
        ),
        (
            "unknown",
            "unknown_boundary_region",
            "region",
            "boundaryUnknown",
            "unknown unresolved region",
            "unknown",
            "grey_region",
            "broken_line",
        ),
        (
            "unmeasured",
            "unmeasured_boundary_fog",
            "fog",
            "boundaryUnmeasured",
            "unmeasured support",
            "unmeasured",
            "fog",
            "dotted_line",
        ),
        (
            "not_computed",
            "not_computed_blocking_wall",
            "wall",
            "boundaryNotComputed",
            "not_computed blocker reason",
            "not_computed",
            "blocking_wall",
            "broken_line",
        ),
        (
            "violated",
            "violated_boundary",
            "broken_boundary",
            "boundaryViolated",
            "violated assumption",
            "violated",
            "red_broken_boundary",
            "broken_line",
        ),
    ];
    json!({
        "sceneId": "boundary-assumption",
        "kind": "boundary_assumption",
        "title": "Boundary",
        "sceneStatus": "active",
        "userQuestion": "Which regions are checked, assumed, unknown, unmeasured, not_computed, or violated?",
        "axisMapping": {
            "x": "evidence contract",
            "y": "assumption status",
            "z": "blocker intensity"
        },
        "primaryRefs": primary_refs,
        "layers": states.iter().map(|(state, layer_kind, geometry_role, click_target_kind, _, _, _, _)| json!({
            "layerId": format!("layer:boundary-assumption:{state}"),
            "kind": layer_kind,
            "boundaryState": state,
            "geometryRole": geometry_role,
            "encodingRef": format!("encoding:boundary-assumption:{state}"),
            "clickTargetKind": click_target_kind,
            "refs": primary_refs,
            "omissionPolicy": "preserve_for_top_insight",
            "animationPurpose": "navigation"
        })).collect::<Vec<_>>(),
        "visualEncodings": states.iter().map(|(state, _, _, _, text_role, color_role, shape_role, line_role)| json!({
            "encodingId": format!("encoding:boundary-assumption:{state}"),
            "boundaryState": state,
            "colorRole": color_role,
            "shapeRole": shape_role,
            "lineRole": line_role,
            "textRole": text_role
        })).collect::<Vec<_>>(),
        "boundaryDigestRef": "boundary-digest:main",
        "nonClaims": [
            "Boundary states qualify the selected measurement profile; they are not inferred source facts.",
            "Unmeasured, unknown, not_computed, and violated states are not measured zero."
        ]
    })
}

fn insight_guided_tours_v1(cards: &[Value]) -> Vec<Value> {
    cards
        .iter()
        .map(|card| {
            let tour_id = format!("tour:{}", string_field(card, "id").trim_start_matches("insight:"));
            json!({
                "tourId": tour_id,
                "title": string_field(card, "title"),
                "insightRefs": [string_field(card, "id")],
                "steps": [
                    {
                        "sceneId": "site-cover",
                        "caption": "These contexts form the selected cover.",
                        "highlightRefs": card["viewerNavigation"]["highlightRefs"]
                    },
                    {
                        "sceneId": card["viewerNavigation"]["sceneId"],
                        "caption": "This scene highlights the measured support or blocker.",
                        "highlightRefs": card["viewerNavigation"]["highlightRefs"]
                    },
                    {
                        "sceneId": "source-evidence",
                        "caption": "These source refs ground the insight.",
                        "highlightRefs": card["viewerNavigation"]["highlightRefs"]
                    },
                    {
                        "sceneId": "boundary-assumption",
                        "caption": "This boundary explains what is checked, assumed, unknown, unmeasured, or not_computed.",
                        "highlightRefs": card["viewerNavigation"]["highlightRefs"]
                    }
                ]
            })
        })
        .collect()
}

fn insight_copy_blocks_v1(
    normalized: &NormalizedArchMapV2,
    cards: &[Value],
    boundary_digest: &Value,
) -> Value {
    let mut source_refs = cards
        .iter()
        .flat_map(|card| string_array_at(card, &["evidence", "sourceRefs"]))
        .chain(top_source_refs(normalized))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    source_refs.truncate(20);
    json!({
        "sourceRefs": source_refs,
        "llmHandoff": {
            "instruction": "Use the following ArchSig result as bounded evidence. Do not infer beyond the listed claims and boundaries.",
            "boundary": boundary_digest["shortText"],
            "topInsights": cards.iter().take(3).map(|card| string_field(card, "oneLine")).collect::<Vec<_>>()
        }
    })
}

fn insight_refs_for_row(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    row: &AgStructuralVerdictV1,
) -> (
    Vec<String>,
    Vec<String>,
    Vec<String>,
    Vec<String>,
    Vec<String>,
    Vec<String>,
    Vec<String>,
) {
    let row_invariants = invariant_values_for_row(packet, row);
    let mut packet_atom_refs = collect_packet_refs_from_values(
        &row_invariants,
        &[
            "supportAtomRefs",
            "mismatchSupportRefs",
            "witnessSupportRefs",
            "atomRefs",
            "atomRef",
        ],
    );
    packet_atom_refs.extend(atom_refs_for_row(normalized, row));
    let atom_refs = normalize_atom_refs(normalized, packet_atom_refs);
    let mut context_refs = context_refs_for_atoms(normalized, &atom_refs);
    context_refs.extend(normalize_context_refs(
        normalized,
        collect_packet_refs_from_values(
            &row_invariants,
            &[
                "contextRefs",
                "contextRef",
                "selectedContexts",
                "sourceContext",
                "targetContext",
            ],
        ),
    ));
    context_refs = sorted_truncated(context_refs, 8);
    let mut source_refs = source_refs_for_atoms(normalized, &atom_refs);
    source_refs.extend(
        collect_packet_refs_from_values(&row_invariants, &["sourceRefs", "sourceRef"])
            .into_iter()
            .map(|source_ref| sanitize_source_ref(&source_ref)),
    );
    source_refs = sorted_truncated(source_refs, 10);
    let mut target_refs = atom_refs.clone();
    target_refs.extend(context_refs.clone());
    if target_refs.is_empty() {
        target_refs.push(structural_verdict_ref(row));
    }
    (
        invariant_refs_for_values(&row_invariants),
        analytic_reading_refs_for_row(packet, row),
        assumption_refs(packet),
        source_refs,
        atom_refs,
        context_refs,
        target_refs,
    )
}

fn atom_refs_for_row(normalized: &NormalizedArchMapV2, row: &AgStructuralVerdictV1) -> Vec<String> {
    let evaluator_hint = evaluator_hint(&row.evaluator);
    let refs = normalized
        .atoms
        .iter()
        .filter(|atom| {
            evaluator_hint
                .is_some_and(|hint| atom.axis.contains(hint) || atom.predicate.contains(hint))
                || row
                    .verdict_data
                    .cert_ref
                    .as_deref()
                    .is_some_and(|cert| cert.contains(&atom.source_atom_id))
        })
        .map(|atom| atom.normalized_atom_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    refs.into_iter().take(12).collect()
}

fn context_refs_for_atoms(normalized: &NormalizedArchMapV2, atom_refs: &[String]) -> Vec<String> {
    let atoms = atom_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let mut refs = normalized
        .contexts
        .iter()
        .filter(|context| {
            context
                .atom_ids
                .iter()
                .any(|atom| atoms.contains(atom.as_str()))
        })
        .map(|context| context.normalized_context_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    refs.truncate(8);
    refs
}

fn source_refs_for_atoms(normalized: &NormalizedArchMapV2, atom_refs: &[String]) -> Vec<String> {
    let atoms = atom_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let mut refs = normalized
        .atoms
        .iter()
        .filter(|atom| atoms.contains(atom.normalized_atom_id.as_str()))
        .flat_map(|atom| {
            atom.source_refs
                .iter()
                .map(|source_ref| sanitize_source_ref(source_ref))
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    refs.truncate(10);
    refs
}

fn structural_verdict_ref(row: &AgStructuralVerdictV1) -> String {
    format!(
        "structuralVerdict/{}/{}/{}",
        stable_ref_segment(&row.evaluator),
        stable_ref_segment(&row.law),
        stable_ref_segment(&row.verdict_data.method_status)
    )
}

fn stable_ref_segment(value: &str) -> String {
    value
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '-' })
        .collect::<String>()
        .trim_matches('-')
        .to_string()
}

fn evaluator_hint(evaluator: &str) -> Option<&'static str> {
    if evaluator.contains("cech") {
        Some("cech")
    } else if evaluator.contains("square-free") || evaluator.contains("square_free") {
        Some("square")
    } else if evaluator.contains("tor") {
        Some("tor")
    } else if evaluator.contains("laplacian") {
        Some("laplacian")
    } else if evaluator.contains("period") {
        Some("period")
    } else if evaluator.contains("transfer") {
        Some("transfer")
    } else {
        None
    }
}

fn invariant_values_for_row(
    packet: &ArchSigMeasurementPacketV1,
    row: &AgStructuralVerdictV1,
) -> Vec<Value> {
    let cert_invariant = row
        .verdict_data
        .cert_ref
        .as_deref()
        .and_then(|cert_ref| cert_ref.strip_prefix("computedInvariants/"));
    let hint = evaluator_hint(&row.evaluator);
    packet
        .computed_invariants
        .iter()
        .filter(|value| {
            let invariant_id = value["invariantId"].as_str().unwrap_or_default();
            cert_invariant.is_some_and(|cert| cert == invariant_id)
                || value["evaluator"].as_str() == Some(row.evaluator.as_str())
                || hint.is_some_and(|hint| invariant_id.contains(hint))
        })
        .cloned()
        .collect()
}

fn invariant_refs_for_values(values: &[Value]) -> Vec<String> {
    values
        .iter()
        .filter_map(|value| value["invariantId"].as_str())
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(12)
        .collect()
}

fn analytic_reading_refs_for_row(
    packet: &ArchSigMeasurementPacketV1,
    row: &AgStructuralVerdictV1,
) -> Vec<String> {
    packet
        .analytic_readings
        .iter()
        .filter(|reading| {
            reading.evaluator == row.evaluator
                || reading.structural_verdict_ref.as_deref() == row.verdict_data.cert_ref.as_deref()
                || evaluator_hint(&row.evaluator)
                    .is_some_and(|hint| reading.reading_id.contains(hint))
        })
        .map(|reading| reading.reading_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(12)
        .collect()
}

fn collect_packet_refs_from_values(values: &[Value], keys: &[&str]) -> Vec<String> {
    let key_set = keys.iter().copied().collect::<BTreeSet<_>>();
    let mut refs = BTreeSet::new();
    for value in values {
        collect_packet_refs(value, &key_set, &mut refs);
    }
    refs.into_iter().collect()
}

fn collect_packet_refs(value: &Value, keys: &BTreeSet<&str>, refs: &mut BTreeSet<String>) {
    match value {
        Value::Object(object) => {
            for (key, nested) in object {
                if keys.contains(key.as_str()) {
                    collect_strings(nested, refs);
                }
                collect_packet_refs(nested, keys, refs);
            }
        }
        Value::Array(items) => {
            for item in items {
                collect_packet_refs(item, keys, refs);
            }
        }
        _ => {}
    }
}

fn collect_strings(value: &Value, refs: &mut BTreeSet<String>) {
    match value {
        Value::String(value) => {
            refs.insert(value.clone());
        }
        Value::Array(items) => {
            for item in items {
                collect_strings(item, refs);
            }
        }
        _ => {}
    }
}

fn normalize_atom_refs(normalized: &NormalizedArchMapV2, refs: Vec<String>) -> Vec<String> {
    let by_source = normalized
        .atoms
        .iter()
        .map(|atom| {
            (
                atom.source_atom_id.as_str(),
                atom.normalized_atom_id.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let normalized_ids = normalized
        .atoms
        .iter()
        .map(|atom| atom.normalized_atom_id.as_str())
        .collect::<BTreeSet<_>>();
    refs.into_iter()
        .filter_map(|atom_ref| {
            if normalized_ids.contains(atom_ref.as_str()) {
                Some(atom_ref)
            } else {
                by_source.get(atom_ref.as_str()).cloned()
            }
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(12)
        .collect()
}

fn normalize_context_refs(normalized: &NormalizedArchMapV2, refs: Vec<String>) -> Vec<String> {
    let by_source = normalized
        .contexts
        .iter()
        .map(|context| {
            (
                context.source_context_id.as_str(),
                context.normalized_context_id.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let normalized_ids = normalized
        .contexts
        .iter()
        .map(|context| context.normalized_context_id.as_str())
        .collect::<BTreeSet<_>>();
    refs.into_iter()
        .filter_map(|context_ref| {
            if normalized_ids.contains(context_ref.as_str()) {
                Some(context_ref)
            } else {
                by_source.get(context_ref.as_str()).cloned()
            }
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(8)
        .collect()
}

fn sorted_truncated(refs: Vec<String>, limit: usize) -> Vec<String> {
    refs.into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(limit)
        .collect()
}

fn sanitize_source_ref(source_ref: &str) -> String {
    if source_ref.starts_with('/')
        || source_ref.contains("\\")
        || source_ref.contains("/Users/")
        || source_ref.contains(".codex")
        || source_ref.contains("Documents/LEAN")
        || source_ref.contains("HelloLean")
    {
        "source-ref:redacted-local-path".to_string()
    } else {
        source_ref.to_string()
    }
}

fn invariant_refs(packet: &ArchSigMeasurementPacketV1) -> Vec<String> {
    packet
        .computed_invariants
        .iter()
        .filter_map(|value| value["invariantId"].as_str())
        .map(ToOwned::to_owned)
        .take(12)
        .collect()
}

fn analytic_reading_refs(packet: &ArchSigMeasurementPacketV1) -> Vec<String> {
    packet
        .analytic_readings
        .iter()
        .map(|reading| reading.reading_id.clone())
        .take(12)
        .collect()
}

fn assumption_refs(packet: &ArchSigMeasurementPacketV1) -> Vec<String> {
    packet
        .assumptions
        .iter()
        .map(|assumption| assumption.theorem_ref.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn evaluator_refs(packet: &ArchSigMeasurementPacketV1) -> Vec<String> {
    packet
        .structural_verdict
        .iter()
        .map(|row| row.evaluator.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn top_atom_refs(normalized: &NormalizedArchMapV2) -> Vec<String> {
    normalized
        .atoms
        .iter()
        .map(|atom| atom.normalized_atom_id.clone())
        .take(8)
        .collect()
}

fn top_context_refs(normalized: &NormalizedArchMapV2) -> Vec<String> {
    normalized
        .contexts
        .iter()
        .map(|context| context.normalized_context_id.clone())
        .take(8)
        .collect()
}

fn top_source_refs(normalized: &NormalizedArchMapV2) -> Vec<String> {
    normalized
        .atoms
        .iter()
        .flat_map(|atom| {
            atom.source_refs
                .iter()
                .map(|source_ref| sanitize_source_ref(source_ref))
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(12)
        .collect()
}

fn insight_sample_refs(normalized: &NormalizedArchMapV2) -> Value {
    json!({
        "atomRefs": top_atom_refs(normalized),
        "contextRefs": top_context_refs(normalized),
        "sourceRefs": top_source_refs(normalized),
        "note": "Sample refs support orientation only; measured insight evidence is listed under evidence."
    })
}

fn assumption_row(row: &AgAssumptionLedgerEntryV1) -> Value {
    json!({
        "theoremRef": row.theorem_ref,
        "assumption": row.assumption,
        "status": row.status,
        "checkedBy": row.checked_by,
        "assumedBy": row.assumed_by
    })
}

fn insight_rank(card: &Value) -> usize {
    match string_field(card, "kind").as_str() {
        "validation_failure" => 800,
        "global_glue_mismatch" => 700,
        "not_computed_blocker" => 650,
        "repair_lower_bound" | "minimal_repair_candidate" => 600,
        "policy_conflict" => 500,
        "architecture_debt_mass" => 400,
        "measurement_boundary" => 300,
        "no_measured_glue_mismatch" => 250,
        _ => 100,
    }
}

fn insight_decision_state(card: &Value) -> &'static str {
    match string_field(card, "severity").as_str() {
        "high" => "needs_attention",
        "medium" => "review_boundary",
        _ => "informational",
    }
}

fn empty_insight_evidence() -> Value {
    json!({
        "structuralVerdictRefs": [],
        "computedInvariantRefs": [],
        "analyticReadingRefs": [],
        "assumptionRefs": [],
        "sourceRefs": [],
        "atomRefs": [],
        "contextRefs": [],
        "coverRefs": [],
        "evaluatorRefs": []
    })
}

fn empty_highlight_refs() -> Value {
    json!({
        "atomRefs": [],
        "contextRefs": [],
        "sourceRefs": []
    })
}

fn string_field(value: &Value, field: &str) -> String {
    value[field].as_str().unwrap_or_default().to_string()
}

fn string_at(value: &Value, path: &[&str]) -> String {
    let mut current = value;
    for key in path {
        current = &current[*key];
    }
    current
        .as_str()
        .map(ToOwned::to_owned)
        .unwrap_or_else(|| current.to_string())
}

fn number_at(value: &Value, path: &[&str]) -> u64 {
    let mut current = value;
    for key in path {
        current = &current[*key];
    }
    current.as_u64().unwrap_or(0)
}

fn string_array_at(value: &Value, path: &[&str]) -> Vec<String> {
    let mut current = value;
    for key in path {
        current = &current[*key];
    }
    current
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|value| value.as_str().map(ToOwned::to_owned))
        .collect()
}

fn slug(value: &str) -> String {
    value
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '-' })
        .collect()
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
    let cover_nerve_projection =
        cover_nerve_projection_v1(normalized, &selected_contexts, &edges, &profile.cover_ref);
    let cover_nerve_face_count = cover_nerve_projection["faces"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
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
                "claimScope": "selected-cover 1-skeleton Cech cochain calculation",
                "selectedCoverRef": profile.cover_ref,
                "coefficient": profile.coefficient,
                "contextCount": selected_contexts.len(),
                "restrictionEdgeCount": edges.len(),
                "coverNerveProjection": cover_nerve_projection,
                "rankD0": selected_contexts.len().saturating_sub(component_count),
                "dimensions": {
                    "H0": h0_dimension,
                    "H1": h1_dimension
                },
                "selectedH2": {
                    "dimension": if cover_nerve_face_count == 0 { json!(0) } else { Value::Null },
                    "status": if cover_nerve_face_count == 0 {
                        "computed_for_selected_1_skeleton"
                    } else {
                        "not_measured_for_triple_overlap_faces"
                    },
                    "reason": if cover_nerve_face_count == 0 {
                        "no selected 2-simplices are present in the finite incidence graph complex"
                    } else {
                        "triple-overlap faces are projected for viewer geometry only; H2 coherence remains outside this measurement"
                    }
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

fn validate_tor_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
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
                "ag.law-conflict-tor@1 requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if !matches!(profile.resolution_selector.as_str(), "taylor@1" | "scarf@1") {
        return Err(format!(
            "ag.law-conflict-tor@1 requires MeasurementProfile resolutionSelector=taylor@1 or scarf@1, found {}",
            profile.resolution_selector
        ));
    }
    if tor_witness_variables(profile).is_empty() {
        return Err(format!(
            "ag.law-conflict-tor@1 requires MeasurementProfile {} witnessFamily law ag.law-conflict-tor",
            profile.profile_id
        ));
    }
    if tor_witness_variables(profile).len() > MAX_TOR_WITNESS_VARIABLES {
        return Err(format!(
            "ag.law-conflict-tor@1 supports at most {MAX_TOR_WITNESS_VARIABLES} witness variables for finite monomial enumeration"
        ));
    }
    Ok(())
}

fn tor_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.law-conflict-tor")
        .map(|witness| witness.variable.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn validate_laplacian_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "R"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "cellular-laplacian@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "analytic-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "analytic-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "analytic-reading@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.sheaf-laplacian@1 requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if laplacian_witness_variables(profile).is_empty() {
        return Err(format!(
            "ag.sheaf-laplacian@1 requires MeasurementProfile {} witnessFamily law ag.sheaf-laplacian",
            profile.profile_id
        ));
    }
    if laplacian_witness_variables(profile).len() > MAX_LAPLACIAN_CELLS {
        return Err(format!(
            "ag.sheaf-laplacian@1 supports at most {MAX_LAPLACIAN_CELLS} witness cells for finite Laplacian enumeration"
        ));
    }
    Ok(())
}

fn validate_period_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "R"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "finite-poset-period@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "analytic-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "analytic-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "analytic-reading@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.period-stokes@1 requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if period_witness_cycles(profile).is_empty() {
        return Err(format!(
            "ag.period-stokes@1 requires MeasurementProfile {} witnessFamily law ag.period-stokes",
            profile.profile_id
        ));
    }
    if period_witness_cycles(profile).len() > MAX_PERIOD_CYCLES {
        return Err(format!(
            "ag.period-stokes@1 supports at most {MAX_PERIOD_CYCLES} witness cycles for finite period enumeration"
        ));
    }
    Ok(())
}

fn validate_transfer_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "R"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "support-localized-transfer@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "analytic-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "analytic-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "analytic-reading@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.support-transfer@1 requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if transfer_witness_targets(profile).is_empty() {
        return Err(format!(
            "ag.support-transfer@1 requires MeasurementProfile {} witnessFamily law ag.support-transfer",
            profile.profile_id
        ));
    }
    if transfer_witness_targets(profile).len() > MAX_TRANSFER_TARGETS {
        return Err(format!(
            "ag.support-transfer@1 supports at most {MAX_TRANSFER_TARGETS} witness targets for finite transfer enumeration"
        ));
    }
    Ok(())
}

fn laplacian_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.sheaf-laplacian")
        .map(|witness| witness.variable.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn period_witness_cycles(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.period-stokes")
        .map(|witness| witness.variable.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn transfer_witness_targets(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.support-transfer")
        .map(|witness| witness.variable.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn laplacian_cells(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
) -> Result<Vec<LaplacianCellV1>, String> {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let mut cells = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "laplacian" && atom.predicate == "cellularCochain")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        if !witness_set.contains(&atom.subject) {
            return Err(format!(
                "ag.sheaf-laplacian@1 cochain {} uses cell outside witnessFamily: {}",
                atom.normalized_atom_id, atom.subject
            ));
        }
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.sheaf-laplacian@1 cochain {} requires numeric object",
                atom.normalized_atom_id
            )
        })?;
        let value = raw.parse::<f64>().map_err(|_| {
            format!(
                "ag.sheaf-laplacian@1 cochain {} has non-numeric object {raw}",
                atom.normalized_atom_id
            )
        })?;
        if !value.is_finite() {
            return Err(format!(
                "ag.sheaf-laplacian@1 cochain {} requires finite numeric object",
                atom.normalized_atom_id
            ));
        }
        if cells
            .iter()
            .any(|cell: &LaplacianCellV1| cell.cell_id == atom.subject)
        {
            return Err(format!(
                "ag.sheaf-laplacian@1 duplicate cellular cochain for {}",
                atom.subject
            ));
        }
        cells.push(LaplacianCellV1 {
            cell_id: atom.subject.clone(),
            value,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    cells.sort_by(|left, right| left.cell_id.cmp(&right.cell_id));
    Ok(cells)
}

fn laplacian_edges(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
) -> Result<Vec<LaplacianEdgeV1>, String> {
    let mut edges = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "laplacian" && atom.predicate == "cellularBoundary")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let target = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.sheaf-laplacian@1 boundary {} requires target cell object",
                atom.normalized_atom_id
            )
        })?;
        edges.push(LaplacianEdgeV1 {
            source: atom.subject.clone(),
            target: target.to_string(),
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    edges.sort_by(|left, right| {
        left.source
            .cmp(&right.source)
            .then_with(|| left.target.cmp(&right.target))
            .then_with(|| left.atom_ref.cmp(&right.atom_ref))
    });
    Ok(edges)
}

fn period_integrals(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    cycle_basis: &[String],
) -> Result<Vec<PeriodIntegralV1>, String> {
    let cycle_set = cycle_basis.iter().cloned().collect::<BTreeSet<_>>();
    let mut pairings = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "period" && atom.predicate == "periodIntegral")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.period-stokes@1 period integral {} requires object cycle=value",
                atom.normalized_atom_id
            )
        })?;
        let (cycle_id, value) = parse_numeric_assignment(
            raw,
            "ag.period-stokes@1 period integral",
            &atom.normalized_atom_id,
        )?;
        if !cycle_set.contains(&cycle_id) {
            return Err(format!(
                "ag.period-stokes@1 period integral {} uses cycle outside witnessFamily: {}",
                atom.normalized_atom_id, cycle_id
            ));
        }
        if pairings.iter().any(|pairing: &PeriodIntegralV1| {
            pairing.form_id == atom.subject && pairing.cycle_id == cycle_id
        }) {
            return Err(format!(
                "ag.period-stokes@1 duplicate period integral for form {} and cycle {}",
                atom.subject, cycle_id
            ));
        }
        pairings.push(PeriodIntegralV1 {
            form_id: atom.subject.clone(),
            cycle_id,
            value,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    pairings.sort_by(|left, right| {
        left.form_id
            .cmp(&right.form_id)
            .then_with(|| left.cycle_id.cmp(&right.cycle_id))
    });
    Ok(pairings)
}

fn stokes_audit_values(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    predicate: &str,
    label: &str,
) -> Result<Vec<StokesAuditValueV1>, String> {
    let mut values = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "period" && atom.predicate == predicate)
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "{label} {} requires object chain=value",
                atom.normalized_atom_id
            )
        })?;
        let (chain_id, value) = parse_numeric_assignment(raw, label, &atom.normalized_atom_id)?;
        if values.iter().any(|entry: &StokesAuditValueV1| {
            entry.form_id == atom.subject && entry.chain_id == chain_id
        }) {
            return Err(format!(
                "{label} duplicate audit value for form {} and chain {}",
                atom.subject, chain_id
            ));
        }
        values.push(StokesAuditValueV1 {
            form_id: atom.subject.clone(),
            chain_id,
            value,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    values.sort_by(|left, right| {
        left.form_id
            .cmp(&right.form_id)
            .then_with(|| left.chain_id.cmp(&right.chain_id))
    });
    Ok(values)
}

fn parse_numeric_assignment(
    raw: &str,
    label: &str,
    atom_ref: &str,
) -> Result<(String, f64), String> {
    let (key, value) = raw.split_once('=').ok_or_else(|| {
        format!("{label} {atom_ref} requires assignment object in key=value form")
    })?;
    let key = key.trim();
    if key.is_empty() {
        return Err(format!(
            "{label} {atom_ref} requires non-empty assignment key"
        ));
    }
    let value = value.trim().parse::<f64>().map_err(|_| {
        format!(
            "{label} {atom_ref} has non-numeric assignment value {}",
            value.trim()
        )
    })?;
    if !value.is_finite() {
        return Err(format!(
            "{label} {atom_ref} requires finite numeric assignment value"
        ));
    }
    Ok((key.to_string(), value))
}

fn stokes_audit_report(
    d_omega: &[StokesAuditValueV1],
    boundary: &[StokesAuditValueV1],
) -> Result<Value, String> {
    let d_map = d_omega
        .iter()
        .map(|entry| ((entry.form_id.clone(), entry.chain_id.clone()), entry))
        .collect::<BTreeMap<_, _>>();
    let boundary_map = boundary
        .iter()
        .map(|entry| ((entry.form_id.clone(), entry.chain_id.clone()), entry))
        .collect::<BTreeMap<_, _>>();
    if d_map.keys().collect::<Vec<_>>() != boundary_map.keys().collect::<Vec<_>>() {
        return Err(
            "ag.period-stokes@1 Stokes audit requires matching dOmegaIntegral and boundaryPeriod keys"
                .to_string(),
        );
    }
    let mut max_abs_residual: f64 = 0.0;
    let mut pairs = Vec::new();
    for (key, left) in d_map {
        let right = boundary_map[&key];
        let residual = left.value - right.value;
        max_abs_residual = max_abs_residual.max(residual.abs());
        if residual.abs() > 1.0e-9 {
            return Err(format!(
                "ag.period-stokes@1 Stokes audit failed for form {} chain {}: dOmega={} boundary={} residual={}",
                left.form_id, left.chain_id, left.value, right.value, residual
            ));
        }
        pairs.push(json!({
            "form": left.form_id,
            "chain": left.chain_id,
            "dOmegaIntegral": round_f64(left.value),
            "boundaryPeriod": round_f64(right.value),
            "residual": round_f64(residual),
            "dOmegaAtomRef": left.atom_ref,
            "boundaryAtomRef": right.atom_ref
        }));
    }
    Ok(json!({
        "identity": "<d omega, gamma> = <omega, boundary gamma>",
        "status": "checked",
        "maxAbsoluteResidual": round_f64(max_abs_residual),
        "pairs": pairs
    }))
}

fn transfer_pairings(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    targets: &[String],
) -> Result<Vec<TransferPairingV1>, String> {
    let target_set = targets.iter().cloned().collect::<BTreeSet<_>>();
    let mut pairings = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "transfer" && atom.predicate == "transferPairing")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.support-transfer@1 transfer pairing {} requires object target=value",
                atom.normalized_atom_id
            )
        })?;
        let (target_id, value) = parse_numeric_assignment(
            raw,
            "ag.support-transfer@1 transfer pairing",
            &atom.normalized_atom_id,
        )?;
        if !target_set.contains(&target_id) {
            return Err(format!(
                "ag.support-transfer@1 transfer pairing {} uses target outside witnessFamily: {}",
                atom.normalized_atom_id, target_id
            ));
        }
        if pairings.iter().any(|pairing: &TransferPairingV1| {
            pairing.path_id == atom.subject && pairing.target_id == target_id
        }) {
            return Err(format!(
                "ag.support-transfer@1 duplicate transfer pairing for path {} and target {}",
                atom.subject, target_id
            ));
        }
        pairings.push(TransferPairingV1 {
            path_id: atom.subject.clone(),
            target_id,
            value,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    pairings.sort_by(|left, right| {
        left.path_id
            .cmp(&right.path_id)
            .then_with(|| left.target_id.cmp(&right.target_id))
    });
    Ok(pairings)
}

fn transfer_repair_paths(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
) -> Result<Vec<TransferRepairPathV1>, String> {
    let mut paths = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "transfer" && atom.predicate == "repairPath")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        if paths
            .iter()
            .any(|path: &TransferRepairPathV1| path.path_id == atom.subject)
        {
            return Err(format!(
                "ag.support-transfer@1 duplicate repair path {}",
                atom.subject
            ));
        }
        paths.push(TransferRepairPathV1 {
            path_id: atom.subject.clone(),
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    paths.sort_by(|left, right| left.path_id.cmp(&right.path_id));
    Ok(paths)
}

fn transfer_ground_costs(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    targets: &[String],
) -> Result<Vec<TransferGroundCostV1>, String> {
    let target_set = targets.iter().cloned().collect::<BTreeSet<_>>();
    let mut costs = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "transfer" && atom.predicate == "groundCost")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        if !target_set.contains(&atom.subject) {
            return Err(format!(
                "ag.support-transfer@1 ground cost {} uses target outside witnessFamily: {}",
                atom.normalized_atom_id, atom.subject
            ));
        }
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.support-transfer@1 ground cost {} requires numeric object",
                atom.normalized_atom_id
            )
        })?;
        let cost = raw.parse::<f64>().map_err(|_| {
            format!(
                "ag.support-transfer@1 ground cost {} has non-numeric object {raw}",
                atom.normalized_atom_id
            )
        })?;
        if !cost.is_finite() || cost < 0.0 {
            return Err(format!(
                "ag.support-transfer@1 ground cost {} requires finite non-negative object",
                atom.normalized_atom_id
            ));
        }
        if costs
            .iter()
            .any(|cost_entry: &TransferGroundCostV1| cost_entry.target_id == atom.subject)
        {
            return Err(format!(
                "ag.support-transfer@1 duplicate ground cost for target {}",
                atom.subject
            ));
        }
        costs.push(TransferGroundCostV1 {
            target_id: atom.subject.clone(),
            cost,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    costs.sort_by(|left, right| left.target_id.cmp(&right.target_id));
    Ok(costs)
}

fn graph_laplacian(
    cell_ids: &[String],
    cell_index: &BTreeMap<String, usize>,
    edges: &[LaplacianEdgeV1],
) -> Vec<Vec<f64>> {
    let mut matrix = vec![vec![0.0; cell_ids.len()]; cell_ids.len()];
    for edge in edges {
        let source = cell_index[&edge.source];
        let target = cell_index[&edge.target];
        if source == target {
            continue;
        }
        matrix[source][source] += 1.0;
        matrix[target][target] += 1.0;
        matrix[source][target] -= 1.0;
        matrix[target][source] -= 1.0;
    }
    matrix
}

fn graph_components(
    cell_count: usize,
    cell_index: &BTreeMap<String, usize>,
    edges: &[LaplacianEdgeV1],
) -> Vec<Vec<usize>> {
    let mut adjacency = vec![Vec::<usize>::new(); cell_count];
    for edge in edges {
        let source = cell_index[&edge.source];
        let target = cell_index[&edge.target];
        adjacency[source].push(target);
        adjacency[target].push(source);
    }
    let mut seen = vec![false; cell_count];
    let mut components = Vec::new();
    for start in 0..cell_count {
        if seen[start] {
            continue;
        }
        let mut stack = vec![start];
        let mut component = Vec::new();
        seen[start] = true;
        while let Some(node) = stack.pop() {
            component.push(node);
            for next in &adjacency[node] {
                if !seen[*next] {
                    seen[*next] = true;
                    stack.push(*next);
                }
            }
        }
        component.sort();
        components.push(component);
    }
    components
}

fn harmonic_projection(values: &[f64], components: &[Vec<usize>]) -> Vec<f64> {
    let mut harmonic = vec![0.0; values.len()];
    for component in components {
        let average =
            component.iter().map(|index| values[*index]).sum::<f64>() / component.len() as f64;
        for index in component {
            harmonic[*index] = average;
        }
    }
    harmonic
}

fn squared_norm(values: &[f64]) -> f64 {
    values.iter().map(|value| value * value).sum()
}

fn jacobi_eigenvalues_symmetric(mut matrix: Vec<Vec<f64>>) -> Vec<f64> {
    let n = matrix.len();
    if n == 0 {
        return Vec::new();
    }
    for _ in 0..64 {
        let mut p = 0;
        let mut q = 0;
        let mut max_value = 0.0;
        for i in 0..n {
            for j in (i + 1)..n {
                let value = matrix[i][j].abs();
                if value > max_value {
                    max_value = value;
                    p = i;
                    q = j;
                }
            }
        }
        if max_value < 1.0e-10 {
            break;
        }
        let tau = (matrix[q][q] - matrix[p][p]) / (2.0 * matrix[p][q]);
        let t = if tau >= 0.0 {
            1.0 / (tau + (1.0 + tau * tau).sqrt())
        } else {
            -1.0 / (-tau + (1.0 + tau * tau).sqrt())
        };
        let c = 1.0 / (1.0 + t * t).sqrt();
        let s = t * c;
        let app = matrix[p][p];
        let aqq = matrix[q][q];
        let apq = matrix[p][q];
        matrix[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq;
        matrix[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq;
        matrix[p][q] = 0.0;
        matrix[q][p] = 0.0;
        for r in 0..n {
            if r == p || r == q {
                continue;
            }
            let arp = matrix[r][p];
            let arq = matrix[r][q];
            matrix[r][p] = c * arp - s * arq;
            matrix[p][r] = matrix[r][p];
            matrix[r][q] = s * arp + c * arq;
            matrix[q][r] = matrix[r][q];
        }
    }
    let mut eigenvalues = (0..n)
        .map(|index| round_f64(matrix[index][index]))
        .collect::<Vec<_>>();
    eigenvalues.sort_by(|left, right| left.total_cmp(right));
    eigenvalues
}

fn rounded_vec(values: &[f64]) -> Vec<Value> {
    values
        .iter()
        .map(|value| json!(round_f64(*value)))
        .collect()
}

fn rounded_matrix(values: &[Vec<f64>]) -> Vec<Vec<Value>> {
    values.iter().map(|row| rounded_vec(row)).collect()
}

fn round_f64(value: f64) -> f64 {
    if value.abs() < 1.0e-9 {
        0.0
    } else {
        (value * 1_000_000.0).round() / 1_000_000.0
    }
}

fn laplacian_assumptions(
    profile: &MeasurementProfileV1,
    cellular_model_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/8.1".to_string(),
            assumption: "finite cellular measurement model selected by MeasurementProfile"
                .to_string(),
            status: cellular_model_status.to_string(),
            checked_by: (cellular_model_status == "checked")
                .then(|| format!("measurement-profile:{}.witnessFamily", profile.profile_id)),
            assumed_by: (cellular_model_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/8.5".to_string(),
            assumption: "finite Hodge decomposition is analytic reading only".to_string(),
            status: "checked".to_string(),
            checked_by: Some("finite-graph-laplacian@1".to_string()),
            assumed_by: None,
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/8.6".to_string(),
            assumption: "harmonic debt minimality remains theorem-candidate".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn period_assumptions(
    profile: &MeasurementProfileV1,
    period_model_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part7/5.2A".to_string(),
            assumption: "finite poset period model selected by MeasurementProfile".to_string(),
            status: period_model_status.to_string(),
            checked_by: (period_model_status == "checked")
                .then(|| format!("measurement-profile:{}.witnessFamily", profile.profile_id)),
            assumed_by: (period_model_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part12/12.3".to_string(),
            assumption: "Stokes audit identity checked on supplied finite model".to_string(),
            status: period_model_status.to_string(),
            checked_by: (period_model_status == "checked")
                .then(|| "finite-poset-period-stokes@1".to_string()),
            assumed_by: (period_model_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part7/5.2A".to_string(),
            assumption: "period_comparison".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn transfer_assumptions(
    profile: &MeasurementProfileV1,
    transfer_model_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/10.1".to_string(),
            assumption: "finite support-localized transfer model selected by MeasurementProfile"
                .to_string(),
            status: transfer_model_status.to_string(),
            checked_by: (transfer_model_status == "checked")
                .then(|| format!("measurement-profile:{}.witnessFamily", profile.profile_id)),
            assumed_by: (transfer_model_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/10.6".to_string(),
            assumption: "finite Wasserstein transfer cost computed on supplied ground costs"
                .to_string(),
            status: transfer_model_status.to_string(),
            checked_by: (transfer_model_status == "checked")
                .then(|| "finite-support-localized-transfer@1".to_string()),
            assumed_by: (transfer_model_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/10.4".to_string(),
            assumption: "transfer_lower_bound".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn tor_common_ambient(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
) -> Result<Option<TorCommonAmbientV1>, String> {
    let ambients = normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "tor" && atom.predicate == "commonAmbient")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .map(|atom| {
            let raw_pair = atom.object.as_deref().ok_or_else(|| {
                format!(
                    "ag.law-conflict-tor@1 common ambient {} requires object law pair",
                    atom.normalized_atom_id
                )
            })?;
            let law_pair = raw_pair
                .split(',')
                .map(str::trim)
                .filter(|law| !law.is_empty())
                .map(ToString::to_string)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            if law_pair.len() != 2 {
                return Err(format!(
                    "ag.law-conflict-tor@1 common ambient {} requires exactly two laws in object",
                    atom.normalized_atom_id
                ));
            }
            Ok(TorCommonAmbientV1 {
                ambient_ref: atom.subject.clone(),
                atom_ref: atom.normalized_atom_id.clone(),
                law_pair,
                source_refs: atom.source_refs.clone(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    if ambients.len() > 1 {
        return Err(format!(
            "ag.law-conflict-tor@1 expected at most one selected common ambient, found {}",
            ambients.len()
        ));
    }

    Ok(ambients.into_iter().next())
}

fn tor_ideal_generators(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
) -> Result<Vec<TorIdealGeneratorV1>, String> {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let mut generators = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "tor" && atom.predicate == "lawIdealGenerator")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let support = tor_atom_variables(atom);
        let unknown = support
            .iter()
            .filter(|variable| !witness_set.contains(*variable))
            .cloned()
            .collect::<Vec<_>>();
        if !unknown.is_empty() {
            return Err(format!(
                "ag.law-conflict-tor@1 generator {} contains variables outside witnessFamily: {}",
                atom.normalized_atom_id,
                unknown.join(",")
            ));
        }
        if support.is_empty() {
            return Err(format!(
                "ag.law-conflict-tor@1 generator {} has no Tor witness variables",
                atom.normalized_atom_id
            ));
        }
        generators.push(TorIdealGeneratorV1 {
            law: atom.subject.clone(),
            generator_id: atom.normalized_atom_id.clone(),
            support,
            context_refs: atom.context_memberships.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    generators.sort_by(|left, right| {
        left.law
            .cmp(&right.law)
            .then_with(|| left.generator_id.cmp(&right.generator_id))
    });
    Ok(generators)
}

fn tor_atom_variables(atom: &crate::NormalizedAtomV2) -> Vec<String> {
    atom.object
        .as_deref()
        .unwrap_or_default()
        .split(',')
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(ToString::to_string)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn tor_conflict_classes(
    generators: &[TorIdealGeneratorV1],
    left_law: &str,
    right_law: &str,
) -> Vec<TorConflictClassV1> {
    let left_generators = generators
        .iter()
        .filter(|generator| generator.law == left_law)
        .collect::<Vec<_>>();
    let right_generators = generators
        .iter()
        .filter(|generator| generator.law == right_law)
        .collect::<Vec<_>>();
    let mut classes = Vec::new();
    for left in &left_generators {
        for right in &right_generators {
            let shared_support = left
                .support
                .iter()
                .filter(|variable| right.support.contains(*variable))
                .cloned()
                .collect::<Vec<_>>();
            if shared_support.is_empty() {
                continue;
            }
            let mut support = left
                .support
                .iter()
                .chain(right.support.iter())
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            support.sort();
            let context_refs = left
                .context_refs
                .iter()
                .chain(right.context_refs.iter())
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            let source_refs = left
                .source_refs
                .iter()
                .chain(right.source_refs.iter())
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            classes.push(TorConflictClassV1 {
                conflict_id: format!("LawConflict_1:{}", classes.len() + 1),
                degree: 1,
                support,
                shared_support,
                left_law: left.law.clone(),
                left_generator_ref: left.generator_id.clone(),
                right_law: right.law.clone(),
                right_generator_ref: right.generator_id.clone(),
                context_refs,
                source_refs,
            });
        }
    }
    classes
}

fn tor_assumptions(
    profile: &MeasurementProfileV1,
    ambient: Option<&TorCommonAmbientV1>,
    ambient_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/9.1".to_string(),
            assumption: "common ambient pair supplied by ArchMap under MeasurementProfile"
                .to_string(),
            status: ambient_status.to_string(),
            checked_by: ambient.map(|ambient| ambient.atom_ref.clone()),
            assumed_by: (ambient_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part5/5.5".to_string(),
            assumption:
                "finite monomial law ideals selected for degree-1 shared-support conflict detection"
                    .to_string(),
            status: "checked".to_string(),
            checked_by: Some(format!(
                "measurement-profile:{}.witnessFamily",
                profile.profile_id
            )),
            assumed_by: None,
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/9.2".to_string(),
            assumption: "flat base change stability is theorem-candidate only".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
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
    minimal_forbidden_supports: &[Vec<String>],
    repair_hitting_sets: &[Vec<String>],
    generators: &[SquareFreeGeneratorV1],
    witness_variable_count: usize,
) -> Result<Option<SquareFreeCertificateV1>, String> {
    let certificates = normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "square-free" && atom.predicate == "nsdepthCertificate")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .map(|atom| {
            let raw = atom.object.as_deref();
            let verification = verify_square_free_nsdepth_certificate(
                raw,
                minimal_forbidden_supports,
                repair_hitting_sets,
                generators,
                witness_variable_count,
            );
            let support_atom_refs = if verification.support_atom_refs.is_empty() {
                vec![atom.normalized_atom_id.clone()]
            } else {
                verification.support_atom_refs.clone()
            };
            SquareFreeCertificateV1 {
                cert_ref: atom.normalized_atom_id.clone(),
                nsdepth: verification.nsdepth,
                support_atom_refs,
                verified_minimal_forbidden_supports: verification
                    .verified_minimal_forbidden_supports,
                status: verification.status,
                effect: verification.effect,
            }
        })
        .collect::<Vec<_>>();

    if certificates.len() > 1 {
        return Err(format!(
            "ag.square-free-repair@1 expected at most one selected NSdepth certificate, found {}",
            certificates.len()
        ));
    }

    Ok(certificates.into_iter().next())
}

#[derive(Debug, Clone)]
struct SquareFreeCertificateVerificationV1 {
    nsdepth: Option<usize>,
    support_atom_refs: Vec<String>,
    verified_minimal_forbidden_supports: Vec<Vec<String>>,
    status: String,
    effect: String,
}

fn verify_square_free_nsdepth_certificate(
    raw: Option<&str>,
    minimal_forbidden_supports: &[Vec<String>],
    repair_hitting_sets: &[Vec<String>],
    generators: &[SquareFreeGeneratorV1],
    witness_variable_count: usize,
) -> SquareFreeCertificateVerificationV1 {
    let Some(raw) = raw.map(str::trim).filter(|value| !value.is_empty()) else {
        return square_free_certificate_unverified(
            None,
            "invalid_payload",
            "NSdepth certificate object is missing; structural verdict remains unknown",
        );
    };

    if let Ok(nsdepth) = raw.parse::<usize>() {
        if nsdepth == 0 {
            return square_free_certificate_unverified(
                None,
                "invalid_payload",
                "NSdepth certificate numeric object must be positive; structural verdict remains unknown",
            );
        }
        return square_free_certificate_unverified(
            Some(nsdepth),
            "author_supplied_unverified",
            "NSdepth certificate only supplies a numeric value, not a finite verifier payload; structural verdict remains unknown",
        );
    }

    let fields = match parse_square_free_certificate_fields(raw) {
        Ok(fields) => fields,
        Err(reason) => {
            return square_free_certificate_unverified(
                None,
                "invalid_payload",
                &format!("{reason}; structural verdict remains unknown"),
            );
        }
    };
    let nsdepth = match fields
        .get("nsdepth")
        .and_then(|value| value.as_str().parse::<usize>().ok())
    {
        Some(nsdepth) if nsdepth > 0 => nsdepth,
        _ => {
            return square_free_certificate_unverified(
                None,
                "invalid_payload",
                "NSdepth verifier payload requires positive nsdepth field; structural verdict remains unknown",
            );
        }
    };
    if nsdepth > witness_variable_count {
        return square_free_certificate_unverified(
            Some(nsdepth),
            "invalid_payload",
            "NSdepth verifier payload exceeds selected witness family size; structural verdict remains unknown",
        );
    }
    let Some(depth_rule) = fields.get("depthRule") else {
        return square_free_certificate_unverified(
            Some(nsdepth),
            "invalid_payload",
            "NSdepth verifier payload requires depthRule field; structural verdict remains unknown",
        );
    };
    if depth_rule != "alexanderDualMaxMinimalHittingSet@1" {
        return square_free_certificate_unverified(
            Some(nsdepth),
            "invalid_payload",
            "NSdepth verifier payload uses unsupported depthRule; structural verdict remains unknown",
        );
    }
    let expected_nsdepth = repair_hitting_sets.iter().map(Vec::len).max().unwrap_or(0);
    if nsdepth != expected_nsdepth {
        return square_free_certificate_unverified(
            Some(nsdepth),
            "invalid_payload",
            "NSdepth verifier payload value does not match the selected finite depthRule; structural verdict remains unknown",
        );
    }

    let payload_supports = fields
        .get("minimalForbiddenSupports")
        .map(|value| parse_square_free_support_payload(value.as_str()))
        .unwrap_or_default();
    let support_atom_refs = fields
        .get("supportAtomRefs")
        .map(|value| parse_csv_values(value.as_str()))
        .unwrap_or_default();
    let expected_atom_refs = generators
        .iter()
        .map(|generator| generator.generator_id.clone())
        .collect::<Vec<_>>();
    if payload_supports != minimal_forbidden_supports {
        return square_free_certificate_unverified(
            Some(nsdepth),
            "invalid_payload",
            "NSdepth verifier payload minimalForbiddenSupports does not match the computed obstruction ideal; structural verdict remains unknown",
        );
    }
    if support_atom_refs != expected_atom_refs {
        return square_free_certificate_unverified(
            Some(nsdepth),
            "invalid_payload",
            "NSdepth verifier payload supportAtomRefs does not match selected obstruction generator atoms; structural verdict remains unknown",
        );
    }

    SquareFreeCertificateVerificationV1 {
        nsdepth: Some(nsdepth),
        support_atom_refs,
        verified_minimal_forbidden_supports: payload_supports,
        status: "verified".to_string(),
        effect:
            "finite verifier payload matched selected obstruction generators, minimal forbidden supports, and depthRule-derived NSdepth; structural verdict is measured_nonzero"
                .to_string(),
    }
}

fn parse_square_free_certificate_fields(raw: &str) -> Result<BTreeMap<String, String>, String> {
    let mut fields = BTreeMap::new();
    let allowed = BTreeSet::from([
        "nsdepth",
        "minimalForbiddenSupports",
        "supportAtomRefs",
        "depthRule",
    ]);
    for segment in raw.split(';') {
        let segment = segment.trim();
        if segment.is_empty() {
            return Err("NSdepth verifier payload contains an empty segment".to_string());
        }
        let Some((key, value)) = segment.split_once('=') else {
            return Err(format!(
                "NSdepth verifier payload segment {segment} must be key=value"
            ));
        };
        let key = key.trim();
        let value = value.trim();
        if key.is_empty() || value.is_empty() {
            return Err("NSdepth verifier payload contains empty key or value".to_string());
        }
        if !allowed.contains(key) {
            return Err(format!(
                "NSdepth verifier payload contains unsupported field {key}"
            ));
        }
        if fields.insert(key.to_string(), value.to_string()).is_some() {
            return Err(format!(
                "NSdepth verifier payload contains duplicate field {key}"
            ));
        }
    }
    Ok(fields)
}

fn square_free_certificate_unverified(
    nsdepth: Option<usize>,
    status: &str,
    effect: &str,
) -> SquareFreeCertificateVerificationV1 {
    SquareFreeCertificateVerificationV1 {
        nsdepth,
        support_atom_refs: Vec::new(),
        verified_minimal_forbidden_supports: Vec::new(),
        status: status.to_string(),
        effect: effect.to_string(),
    }
}

fn parse_square_free_support_payload(raw: &str) -> Vec<Vec<String>> {
    let mut supports = raw
        .split('|')
        .map(parse_plus_values)
        .filter(|support| !support.is_empty())
        .collect::<Vec<_>>();
    for support in &mut supports {
        support.sort();
        support.dedup();
    }
    supports.sort();
    supports.dedup();
    supports
}

fn parse_plus_values(raw: &str) -> Vec<String> {
    let mut values = raw
        .split('+')
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    values.sort();
    values.dedup();
    values
}

fn parse_csv_values(raw: &str) -> Vec<String> {
    let mut values = raw
        .split(',')
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    values.sort();
    values.dedup();
    values
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

fn cover_nerve_projection_v1(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    cover_ref: &str,
) -> Value {
    let context_atom_refs = context_atom_refs(normalized, selected_contexts);
    let vertices = selected_contexts
        .iter()
        .map(|context| {
            json!({
                "contextRef": context,
                "atomRefs": context_atom_refs.get(context).cloned().unwrap_or_default(),
                "objectKind": "nerveVertex"
            })
        })
        .collect::<Vec<_>>();
    let edge_rows = edges
        .iter()
        .map(|edge| {
            json!({
                "edgeId": edge.edge_id,
                "sourceContextRef": edge.source_context,
                "targetContextRef": edge.target_context,
                "value": edge.value,
                "supportAtomRefs": edge.support_atom_refs,
                "objectKind": "nerveEdge",
                "source": "selected cover restriction edge"
            })
        })
        .collect::<Vec<_>>();
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let mut edge_by_pair = BTreeMap::new();
    for edge in edges {
        edge_by_pair.insert(
            (edge.source_context.clone(), edge.target_context.clone()),
            edge.edge_id.clone(),
        );
        edge_by_pair.insert(
            (edge.target_context.clone(), edge.source_context.clone()),
            edge.edge_id.clone(),
        );
    }
    let atom_refs_by_context = normalized
        .contexts
        .iter()
        .filter(|context| selected.contains(&context.normalized_context_id))
        .map(|context| {
            (
                context.normalized_context_id.clone(),
                context.atom_ids.iter().cloned().collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut faces = Vec::new();
    for left in 0..selected_contexts.len() {
        for middle in left + 1..selected_contexts.len() {
            for right in middle + 1..selected_contexts.len() {
                let contexts = [
                    selected_contexts[left].clone(),
                    selected_contexts[middle].clone(),
                    selected_contexts[right].clone(),
                ];
                let Some(left_atoms) = atom_refs_by_context.get(&contexts[0]) else {
                    continue;
                };
                let Some(middle_atoms) = atom_refs_by_context.get(&contexts[1]) else {
                    continue;
                };
                let Some(right_atoms) = atom_refs_by_context.get(&contexts[2]) else {
                    continue;
                };
                let shared_atom_refs = left_atoms
                    .intersection(middle_atoms)
                    .cloned()
                    .collect::<BTreeSet<_>>()
                    .intersection(right_atoms)
                    .cloned()
                    .collect::<Vec<_>>();
                if shared_atom_refs.is_empty() {
                    continue;
                }
                let edge_refs = [
                    edge_by_pair
                        .get(&(contexts[0].clone(), contexts[1].clone()))
                        .cloned(),
                    edge_by_pair
                        .get(&(contexts[0].clone(), contexts[2].clone()))
                        .cloned(),
                    edge_by_pair
                        .get(&(contexts[1].clone(), contexts[2].clone()))
                        .cloned(),
                ]
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
                faces.push(json!({
                    "faceId": format!("nerve-face:{}:{}:{}", contexts[0], contexts[1], contexts[2]),
                    "coverRef": cover_ref,
                    "contextRefs": contexts,
                    "edgeRefs": edge_refs,
                    "sharedAtomRefs": shared_atom_refs,
                    "objectKind": "nerveTriangle",
                    "source": "selected cover triple overlap with shared atom refs",
                    "coherenceClaim": "not_visualized"
                }));
            }
        }
    }
    json!({
        "coverRef": cover_ref,
        "vertices": vertices,
        "edges": edge_rows,
        "faces": faces,
        "faceSource": "selected cover triple-overlap sharedAtomRefs recorded in archsig-measurement-packet/v1; not inferred by the viewer",
        "h2CoherenceVisualized": false
    })
}

fn empty_cover_nerve_projection_v1(cover_ref: &str, reason: &str) -> Value {
    json!({
        "coverRef": cover_ref,
        "vertices": [],
        "edges": [],
        "faces": [],
        "faceSource": reason,
        "h2CoherenceVisualized": false,
        "projectionStatus": "not_projected_missing_packet_cover_nerve"
    })
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
    insight_report: &Value,
) -> Value {
    let atom_count = normalized.atoms.len();
    let preserved_atom_refs = top_insight_atom_refs(insight_report);
    let preserved_context_refs = top_insight_context_refs(insight_report);
    let viewer_atoms = projected_atoms(normalized, &preserved_atom_refs, 10_000);
    let viewer_contexts = projected_contexts(normalized, &preserved_context_refs, 20_000);
    let viewer_covers = projected_covers(normalized, 10_000);
    let atom_nodes = viewer_atom_nodes(&viewer_atoms, insight_report);
    let molecule_groups = viewer_molecule_groups(&viewer_contexts);
    let atom_edges = viewer_atom_edges(&viewer_contexts);
    let context_memberships = normalized
        .atoms
        .iter()
        .map(|atom| atom.context_memberships.len())
        .sum::<usize>();
    let cover_overlaps = normalized
        .covers
        .iter()
        .map(|cover| cover.context_ids.len().saturating_sub(1))
        .sum::<usize>();
    let scene_layer_objects = insight_report["viewerVisualScenes"]
        .as_array()
        .into_iter()
        .flatten()
        .flat_map(|scene| scene["layers"].as_array().into_iter().flatten())
        .count();
    let large_graph_mode = atom_count >= 10_000
        || context_memberships > 20_000
        || cover_overlaps > 10_000
        || scene_layer_objects > 1_000;
    let omitted_detail_counts = insight_report["viewerVisualScenes"]
        .as_array()
        .map(|scenes| insight_omitted_detail_counts_v1(normalized, scenes))
        .unwrap_or_else(|| insight_omitted_detail_counts_v1(normalized, &[]));
    json!({
        "schemaVersion": "archsig-atom-viewer-data-v2",
        "sourceArtifactRefs": {
            "normalizedArchMap": "normalized-archmap.json",
            "measurementPacket": "archsig-measurement-packet.json",
            "summary": "archsig-analysis-summary.json",
            "insightReport": "archsig-insight-report.json",
            "insightBrief": "archsig-insight-brief.md"
        },
        "decisionBar": {
            "conclusion": insight_report["headline"]["conclusionCode"],
            "validation": "see archsig-analysis-validation.json",
            "boundaryDigest": insight_report["boundaryDigest"]["shortText"],
            "artifactLinks": insight_report["outputArtifacts"]
        },
        "atomNodes": atom_nodes,
        "moleculeGroups": molecule_groups,
        "atomEdges": atom_edges,
        "insightQueue": insight_report["insightCards"],
        "actionQueue": insight_report["actionQueue"],
        "viewerVisualScenes": insight_report["viewerVisualScenes"],
        "guidedTours": insight_report["guidedTours"],
        "copyBlocks": insight_report["copyBlocks"],
        "aatGeometryOverlays": {
            "schemaVersion": "archsig-aat-geometry-overlays-v1",
            "projectionBoundary": "bounded viewer projection of measured ArchSig AG geometry; visual richness is not a new verdict",
            "gluingGeometry": insight_report["gluingGeometry"],
            "nerve": insight_report["gluingGeometry"]["nerve"],
            "cocycleRibbon": insight_report["gluingGeometry"]["cocycleRibbon"],
            "locusField": insight_report["gluingGeometry"]["locusField"],
            "forbiddenCages": insight_report["gluingGeometry"]["forbiddenCages"],
            "repairMorphs": insight_report["gluingGeometry"]["repairMorphs"],
            "atomGlyphs": insight_report["gluingGeometry"]["atomGlyphs"],
            "omittedGeometryCounts": insight_report["gluingGeometry"]["omittedGeometryCounts"],
            "nonClaims": insight_report["gluingGeometry"]["nonClaims"]
        },
        "reportPane": {
            "conclusion": summary["conclusion"],
            "profileRef": packet.profile.profile_id,
            "assumptionSummary": summary["assumptionSummary"],
            "structuralVerdictSummary": summary["structuralVerdictSummary"],
            "readThisFirst": insight_report["readThisFirst"],
            "insightQueue": insight_report["insightCards"],
            "actionQueue": insight_report["actionQueue"],
            "evidenceDetailShape": ["What", "Why", "Where", "Measurement", "Boundary", "Next"],
            "boundaryDigest": insight_report["boundaryDigest"],
            "omittedDetailCounts": omitted_detail_counts,
            "artifactLinks": insight_report["outputArtifacts"]
        },
        "finitePosetSite": {
            "atoms": viewer_atoms,
            "contexts": viewer_contexts,
            "covers": viewer_covers
        },
        "largeGraphStrategy": {
            "mode": if large_graph_mode { "cluster_aggregation" } else { "full_projection" },
            "thresholds": {
                "fullGeometryAtoms": 2_000,
                "instancedAtoms": 10_000,
                "clusterAtoms": 50_000,
                "contextMemberships": 20_000,
                "coverOverlaps": 10_000,
                "sceneLayerObjects": 1_000
            },
            "topInsightEvidencePinning": {
                "policy": "preserve_for_top_insight",
                "preservedRefs": top_insight_preserved_refs(insight_report),
                "aggregatedRefs": if large_graph_mode { vec!["background-geometry"] } else { Vec::<&str>::new() },
                "omittedRefs": if large_graph_mode { vec!["background-labels"] } else { Vec::<&str>::new() }
            }
        },
        "omittedDetailCounts": insight_report["omittedDetailCounts"],
        "nonConclusions": [
            "Viewer data is a bounded projection of ArchMap v2 and measurement packet foundation rows.",
            "Layout and site visualization are not AG invariant values or Lean proof objects.",
            "Holonomy-like views are restriction path or cover path exploration, not monodromy verdicts.",
            "Theorem-candidate readings are not displayed as structural conclusions."
        ]
    })
}

fn top_insight_preserved_refs(insight_report: &Value) -> Vec<String> {
    let mut refs = BTreeSet::new();
    for value in string_array_at(insight_report, &["headline", "primaryVerdictRefs"]) {
        refs.insert(value);
    }
    if let Some(card) = insight_report["insightCards"]
        .as_array()
        .and_then(|cards| cards.first())
    {
        for path in [
            ["evidence", "structuralVerdictRefs"],
            ["evidence", "computedInvariantRefs"],
            ["evidence", "analyticReadingRefs"],
            ["evidence", "atomRefs"],
            ["evidence", "contextRefs"],
            ["evidence", "sourceRefs"],
            ["nextAction", "targetRefs"],
        ] {
            for value in string_array_at(card, &path) {
                refs.insert(value);
            }
        }
    }
    refs.into_iter().take(32).collect()
}

fn top_insight_atom_refs(insight_report: &Value) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    if let Some(card) = insight_report["insightCards"]
        .as_array()
        .and_then(|cards| cards.first())
    {
        for value in string_array_at(card, &["evidence", "atomRefs"]) {
            refs.insert(value);
        }
        for value in string_array_at(card, &["viewerNavigation", "highlightRefs", "atomRefs"]) {
            refs.insert(value);
        }
    }
    refs
}

fn top_insight_context_refs(insight_report: &Value) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    if let Some(card) = insight_report["insightCards"]
        .as_array()
        .and_then(|cards| cards.first())
    {
        for value in string_array_at(card, &["evidence", "contextRefs"]) {
            refs.insert(value);
        }
        for value in string_array_at(card, &["viewerNavigation", "highlightRefs", "contextRefs"]) {
            refs.insert(value);
        }
    }
    refs
}

fn projected_atoms(
    normalized: &NormalizedArchMapV2,
    preserved_refs: &BTreeSet<String>,
    limit: usize,
) -> Vec<NormalizedAtomV2> {
    let mut selected = Vec::new();
    let mut seen = BTreeSet::new();
    for atom in normalized.atoms.iter().filter(|atom| {
        preserved_refs.contains(atom.normalized_atom_id.as_str())
            || preserved_refs.contains(atom.source_atom_id.as_str())
    }) {
        if seen.insert(atom.normalized_atom_id.clone()) {
            selected.push(sanitize_viewer_atom(atom.clone()));
        }
    }
    for atom in &normalized.atoms {
        if selected.len() >= limit {
            break;
        }
        if seen.insert(atom.normalized_atom_id.clone()) {
            selected.push(sanitize_viewer_atom(atom.clone()));
        }
    }
    selected.truncate(limit);
    selected
}

fn projected_contexts(
    normalized: &NormalizedArchMapV2,
    preserved_refs: &BTreeSet<String>,
    limit: usize,
) -> Vec<NormalizedContextV2> {
    let mut selected = Vec::new();
    let mut seen = BTreeSet::new();
    for context in normalized.contexts.iter().filter(|context| {
        preserved_refs.contains(context.normalized_context_id.as_str())
            || preserved_refs.contains(context.source_context_id.as_str())
    }) {
        if seen.insert(context.normalized_context_id.clone()) {
            selected.push(sanitize_viewer_context(context.clone()));
        }
    }
    for context in &normalized.contexts {
        if selected.len() >= limit {
            break;
        }
        if seen.insert(context.normalized_context_id.clone()) {
            selected.push(sanitize_viewer_context(context.clone()));
        }
    }
    selected.truncate(limit);
    selected
}

fn projected_covers(normalized: &NormalizedArchMapV2, limit: usize) -> Vec<NormalizedCoverV2> {
    normalized
        .covers
        .iter()
        .take(limit)
        .cloned()
        .map(sanitize_viewer_cover)
        .collect()
}

fn viewer_atom_nodes(atoms: &[NormalizedAtomV2], insight_report: &Value) -> Vec<Value> {
    let top_atoms = top_insight_atom_refs(insight_report);
    atoms
        .iter()
        .map(|atom| {
            let source_refs = atom
                .source_refs
                .iter()
                .map(|source_ref| json!({ "ref": source_ref }))
                .collect::<Vec<_>>();
            json!({
                "nodeId": atom.normalized_atom_id,
                "sourceAtomId": atom.source_atom_id,
                "atomKind": atom.atom_kind,
                "atomFamily": atom.atom_kind,
                "subjectRef": atom.subject,
                "axis": atom.axis,
                "predicate": atom.predicate,
                "objectRef": atom.object,
                "observationStatus": atom.normalization_status,
                "normalizationStatus": atom.normalization_status,
                "moleculeMemberships": atom.context_memberships,
                "projectionRefs": atom.context_memberships,
                "sourceRefSamples": source_refs,
                "sourceRefCount": atom.source_refs.len(),
                "objectRefCount": usize::from(atom.object.is_some()),
                "priorityScore": if top_atoms.contains(atom.normalized_atom_id.as_str()) || top_atoms.contains(atom.source_atom_id.as_str()) { 100 } else { 10 },
                "labels": [atom.axis.clone(), atom.predicate.clone()]
            })
        })
        .collect()
}

fn viewer_molecule_groups(contexts: &[NormalizedContextV2]) -> Vec<Value> {
    contexts
        .iter()
        .map(|context| {
            json!({
                "groupId": context.normalized_context_id,
                "sourceMoleculeId": context.source_context_id,
                "atomObservationRefs": context.atom_ids,
                "atomIds": context.atom_ids,
                "generatedMoleculeCandidateStatus": context.poset_status,
                "requiredPortStatus": "not_applicable",
                "compositionStatus": context.poset_status
            })
        })
        .collect()
}

fn viewer_atom_edges(contexts: &[NormalizedContextV2]) -> Vec<Value> {
    let mut edges = Vec::new();
    for context in contexts {
        for target in &context.restricts_to {
            edges.push(json!({
                "edgeId": format!("edge:{}->{}", context.normalized_context_id, target),
                "sourceNodeRef": context.normalized_context_id,
                "targetNodeRef": target,
                "edgeKind": "contextRestriction"
            }));
        }
        for pair in context.atom_ids.windows(2) {
            if let [source, target] = pair {
                edges.push(json!({
                    "edgeId": format!("edge:{}:{}->{}", context.normalized_context_id, source, target),
                    "sourceNodeRef": source,
                    "targetNodeRef": target,
                    "edgeKind": "contextMembership"
                }));
            }
        }
    }
    edges
}

fn sanitize_viewer_atom(mut atom: NormalizedAtomV2) -> NormalizedAtomV2 {
    atom.source_refs = atom
        .source_refs
        .iter()
        .map(|source_ref| sanitize_source_ref(source_ref))
        .collect();
    atom
}

fn sanitize_viewer_context(mut context: NormalizedContextV2) -> NormalizedContextV2 {
    context.source_refs = context
        .source_refs
        .iter()
        .map(|source_ref| sanitize_source_ref(source_ref))
        .collect();
    context
}

fn sanitize_viewer_cover(mut cover: NormalizedCoverV2) -> NormalizedCoverV2 {
    cover.source_refs = cover
        .source_refs
        .iter()
        .map(|source_ref| sanitize_source_ref(source_ref))
        .collect();
    cover
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

    fn normalized_fixture() -> NormalizedArchMapV2 {
        serde_json::from_value(json!({
            "schema": "archmap-normalized/v2",
            "normalizerId": "test-normalizer",
            "sourceArchmapRef": "archmap:test",
            "sourceArchmapId": "archmap:test",
            "extractionDoctrineRef": {
                "doctrineId": "doctrine:test",
                "fingerprint": "sha256:test"
            },
            "atoms": [
                {
                    "sourceAtomId": "x_checkout",
                    "normalizedAtomId": "atom:checkout",
                    "atomKind": "component",
                    "subject": "x_checkout",
                    "axis": "semantic",
                    "predicate": "forbidden_obstruction_marker",
                    "object": null,
                    "sourceRefs": ["fixture://checkout"],
                    "contextMemberships": ["ctx:a", "ctx:b", "ctx:c"],
                    "normalizationStatus": "normalized"
                },
                {
                    "sourceAtomId": "x_inventory",
                    "normalizedAtomId": "atom:inventory",
                    "atomKind": "component",
                    "subject": "x_inventory",
                    "axis": "semantic",
                    "predicate": "service",
                    "object": null,
                    "sourceRefs": ["fixture://inventory"],
                    "contextMemberships": ["ctx:a", "ctx:b", "ctx:c"],
                    "normalizationStatus": "normalized"
                },
                {
                    "sourceAtomId": "x_payment",
                    "normalizedAtomId": "atom:payment",
                    "atomKind": "component",
                    "subject": "x_payment",
                    "axis": "semantic",
                    "predicate": "service",
                    "object": null,
                    "sourceRefs": ["fixture://payment"],
                    "contextMemberships": ["ctx:b", "ctx:c"],
                    "normalizationStatus": "normalized"
                }
            ],
            "contexts": [
                {
                    "sourceContextId": "ctx:a",
                    "normalizedContextId": "ctx:a",
                    "atomIds": ["atom:checkout", "atom:inventory"],
                    "restrictsTo": ["ctx:b"],
                    "sourceRefs": ["fixture://a"],
                    "posetStatus": "selected"
                },
                {
                    "sourceContextId": "ctx:b",
                    "normalizedContextId": "ctx:b",
                    "atomIds": ["atom:checkout", "atom:inventory", "atom:payment"],
                    "restrictsTo": ["ctx:c"],
                    "sourceRefs": ["fixture://b"],
                    "posetStatus": "selected"
                },
                {
                    "sourceContextId": "ctx:c",
                    "normalizedContextId": "ctx:c",
                    "atomIds": ["atom:checkout", "atom:inventory", "atom:payment"],
                    "restrictsTo": [],
                    "sourceRefs": ["fixture://c"],
                    "posetStatus": "selected"
                }
            ],
            "covers": [{
                "sourceCoverId": "cover:test",
                "normalizedCoverId": "cover:test",
                "contextIds": ["ctx:a", "ctx:b", "ctx:c"],
                "sourceRefs": ["fixture://cover"],
                "coverageStatus": "selected"
            }],
            "summary": {
                "atomCount": 3,
                "normalizedAtomCount": 3,
                "contextCount": 3,
                "coverCount": 1,
                "doctrineFingerprint": "sha256:test"
            },
            "nonConclusions": []
        }))
        .expect("normalized fixture parses")
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

    #[test]
    fn gluing_projection_does_not_infer_cover_nerve_without_packet_projection() {
        let normalized = normalized_fixture();
        let packet = packet_fixture();

        let gluing = gluing_geometry_projection_v1(&normalized, &packet);

        assert_eq!(
            gluing["nerve"]["triangles"],
            json!([]),
            "viewer gluing projection must not infer triangle geometry when packet has no coverNerveProjection"
        );
        assert_eq!(
            gluing["nerve"]["triangleSource"],
            "missing packet coverNerveProjection; viewer does not infer cover triangles"
        );
    }

    #[test]
    fn forbidden_cages_do_not_fallback_to_predicate_atoms() {
        let normalized = normalized_fixture();
        let packet = packet_fixture();

        let cages = forbidden_cage_projection(&normalized, &packet);

        assert!(
            cages.is_empty(),
            "predicate names alone must not create forbidden support cages without packet support"
        );
    }

    #[test]
    fn repair_morphs_link_related_forbidden_cages() {
        let normalized = normalized_fixture();
        let mut packet = packet_fixture();
        packet.computed_invariants = vec![json!({
            "invariantId": "square-free-repair:test",
            "obstructionIdeal": {
                "generators": [
                    {
                        "generatorId": "g0",
                        "support": ["x_checkout", "x_inventory"]
                    },
                    {
                        "generatorId": "g1",
                        "support": ["x_inventory", "x_payment"]
                    }
                ]
            },
            "alexanderDualRepair": {
                "minimalHittingSets": [
                    ["x_inventory"],
                    ["x_checkout", "x_payment"]
                ]
            }
        })];

        let cages = forbidden_cage_projection(&normalized, &packet);
        let morphs = repair_morph_projection(&normalized, &packet, &cages);

        assert_eq!(cages.len(), 2);
        assert_eq!(morphs.len(), 2);
        assert!(morphs.iter().all(|morph| {
            morph["fromCageRefs"]
                .as_array()
                .is_some_and(|refs| refs.len() == 2)
                && morph["fromAtomRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty())
        }));
        assert_eq!(
            morphs[1]["fromCageRef"], "forbidden-cage:g1",
            "multiple repair morphs must not all start from the first forbidden cage"
        );
    }
}
