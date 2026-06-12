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
const MAX_TOR_WITNESS_VARIABLES: usize = 12;
const MAX_LAPLACIAN_CELLS: usize = 16;
const MAX_PERIOD_CYCLES: usize = 16;
const MAX_TRANSFER_TARGETS: usize = 16;

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
    nsdepth: usize,
    support_atom_refs: Vec<String>,
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
        method_status: "finite_monomial_tor_computed".to_string(),
        cert_ref: Some(ambient.atom_ref.clone()),
        reason: if has_conflict {
            "finite monomial Tor found LawConflict classes under the supplied common ambient"
                .to_string()
        } else {
            "finite monomial Tor found no LawConflict class under the supplied common ambient"
                .to_string()
        },
        computed_invariants: vec![json!({
            "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
            "evaluator": "ag.law-conflict-tor@1",
            "method": "finite-monomial-tor@1",
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
                "classCount": conflicts.len()
            }],
            "nonConclusions": [
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
        "readingKind": "cellular-sheaf-laplacian@1",
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
            assumption: "finite monomial law ideals selected for Taylor / Scarf Tor enumeration"
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
