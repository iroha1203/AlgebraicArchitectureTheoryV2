use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};

use crate::law_execution::{LawExecutionPlanV1, build_law_execution_plan};
use crate::saga::{evaluate_saga_descent_v1, evaluate_saga_grounded_v1};
use crate::saga_complex::derive_saga_complex_from_normalized;
use crate::validation::{generic_validation_example, validation_check};
use crate::{
    ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE, ARCHSIG_ANALYSIS_CONCLUSION_CODES,
    ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION,
    ARCHSIG_MEASURED_AG_OBSTRUCTION_UNDER_PROFILE, ARCHSIG_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE,
    ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS, ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
    ARCHSIG_NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE, ARCHSIG_REPAIR_TARGETS_IDENTIFIED,
    ARCHSIG_SAGA_MEASURED_NONGLUING_RESIDUAL, ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX,
    ARCHSIG_TWO_PROFILES_REPORTED_SEPARATELY, AgAnalyticReadingV1, AgAssumptionLedgerEntryV1,
    AgStructuralVerdictV1, AgVerdictDataV1, ArchMapDocumentV2, ArchSigMeasurementPacketV1,
    BoundaryStatementV1, LawEquationSurfaceV1, LawPolicyDocumentV1, MeasurementProfileV1,
    MeasurementProfileWitnessV1, NormalizedArchMapV2, NormalizedAtomV2, NormalizedContextV2,
    NormalizedCoverV2, SuppliedDataLedgerEntryV1, ValidationCheck, ValidationExample,
    analytic_claim_status, analytic_fidelity, assumption_id_for_schema,
};

const VERDICTS: [&str; 5] = [
    "measured_zero",
    "measured_nonzero",
    "unmeasured",
    "unknown",
    "not_computed",
];
const STRUCTURAL_VERDICT_EVALUATORS: [&str; 11] = [
    "ag.cech-obstruction",
    "ag.restriction-compatibility",
    "ag.section-factorization",
    "ag.boundary-residue",
    "ag.square-free-repair",
    "ag.law-conflict-tor",
    "ag.coherence-obstruction",
    "ag.sheaf-laplacian",
    "ag.period-stokes-audit",
    "ag.saga-descent",
    "ag.saga-grounded",
];
const COMPUTED_INVARIANT_KINDS: [&str; 18] = [
    "measurement-invariant",
    "cech-h1-rank",
    "minimal-forbidden-supports",
    "tor1-class-support",
    "boundary-residue-rank",
    "residual-boundary-membership",
    "residual-class-support",
    "selected-cover-edge-support",
    "coherence-obstruction-count",
    "restriction-compatibility-rank",
    "section-factorization-rank",
    "sheaf-laplacian-spectrum",
    "period-stokes-pairing",
    "period-stokes-audit",
    "support-transfer-rank",
    "topological-debt-capacity",
    "saga-grounded-defect-quotient",
    "harmonic-debt",
];
const COMPUTED_INVARIANT_KIND_OWNERS: [(&str, &str); 1] =
    [("saga-grounded-defect-quotient", "ag.saga-grounded")];
const MAX_SQUARE_FREE_WITNESS_VARIABLES: usize = 12;
const MAX_COHERENCE_CONTEXTS: usize = 12;
const MAX_TOR_WITNESS_VARIABLES: usize = 12;
const MAX_BOUNDARY_RESIDUE_VARIABLES: usize = 16;
const MAX_LAPLACIAN_CELLS: usize = 16;
const MAX_PERIOD_CYCLES: usize = 16;
const MAX_TRANSFER_TARGETS: usize = 16;
const HARMONIC_COST_MODEL_WHAT_NEXT: &str = "supply analytic.costModel with a positive Lipschitz constant and harmonic resolution before evaluating essentialRepairLowerBound";
const GLUING_TRIANGLE_RENDER_LIMIT: usize = 80;
const GLUING_COCYCLE_EDGE_RENDER_LIMIT: usize = 80;
const GLUING_FIELD_ROW_RENDER_LIMIT: usize = 64;
const GLUING_REGION_RENDER_LIMIT: usize = 24;
const GLUING_CAGE_RENDER_LIMIT: usize = 80;
const GLUING_MORPH_RENDER_LIMIT: usize = 50;
const GLUING_ATOM_GLYPH_RENDER_LIMIT: usize = 2_000;
const ANALYTIC_OVERLAY_RENDER_LIMIT: usize = 80;
const PERIOD_STOKES_METER_RENDER_LIMIT: usize = 24;
const BOUNDARY_STATEMENT_KINDS: [&str; 6] = [
    "silence_by_design",
    "out_of_selected_vocabulary",
    "unmeasured_support",
    "violated_assumption",
    "blocked_method",
    "not_applicable",
];

struct SummaryTranslationRule {
    conclusion_code: &'static str,
    theorem_ref: Option<&'static str>,
    principal_text: &'static str,
    boundary: &'static str,
    generated_discipline: &'static str,
}

fn summary_translation_rule(conclusion: &str) -> SummaryTranslationRule {
    match conclusion {
        ARCHSIG_SAGA_MEASURED_NONGLUING_RESIDUAL => SummaryTranslationRule {
            conclusion_code: ARCHSIG_SAGA_MEASURED_NONGLUING_RESIDUAL,
            theorem_ref: None,
            principal_text: "The derived SAGA residual is measured outside B1 with concrete residual support.",
            boundary: "Revise the observed sections or the derived SAGA complex and re-run analyze before claiming repair gluing.",
            generated_discipline: "generated derived-residual boundary-membership detection",
        },
        ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX => SummaryTranslationRule {
            conclusion_code: ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX,
            theorem_ref: None,
            principal_text: "The derived SAGA residual is measured inside B1 for the finite complex derived from the selected ArchMap cover.",
            boundary: "The gluing reading is relative to the finite complex derived from the selected ArchMap cover and its triple faces; it does not claim global semantic repair.",
            generated_discipline: "generated derived-residual boundary-membership detection",
        },
        ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS => SummaryTranslationRule {
            conclusion_code: ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS,
            theorem_ref: None,
            principal_text: "The selected finite complex contains a measured non-gluing derived residual class in Z1/B1.",
            boundary: "The class reading is relative to the selected cover 1-skeleton, the derived triple faces whose cocycle parity was checked, and the law-surface witness bindings.",
            generated_discipline: "generated derived class representative detection",
        },
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION => SummaryTranslationRule {
            conclusion_code: ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION,
            theorem_ref: Some("part4/12.4"),
            principal_text: "The selected abelian cover shape and explicit restriction-surjectivity witnesses exclude a gluing obstruction in this Stage 1 profile.",
            boundary: "Supply non-abelian torsor, stacky descent, or gerbe data before speaking outside the selected abelian coefficient sheaf.",
            generated_discipline: "generated cover-shape detection",
        },
        ARCHSIG_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE => SummaryTranslationRule {
            conclusion_code: ARCHSIG_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE,
            theorem_ref: Some("part4/12.3"),
            principal_text: "The selected cover has a concrete H1 support measured by the finite F2 Cech detector.",
            boundary: "Supply a different selected cover, coefficient sheaf, or restriction data before changing this profile-relative reading.",
            generated_discipline: "generated Cech support detection",
        },
        ARCHSIG_REPAIR_TARGETS_IDENTIFIED => SummaryTranslationRule {
            conclusion_code: ARCHSIG_REPAIR_TARGETS_IDENTIFIED,
            theorem_ref: Some("part8/5.2"),
            principal_text: "The selected square-free obstruction invariant identifies combinatorial repair target supports.",
            boundary: "Supply semantic repair operations before treating hitting sets as automatic repairs.",
            generated_discipline: "generated square-free hitting-set detection",
        },
        ARCHSIG_TWO_PROFILES_REPORTED_SEPARATELY => SummaryTranslationRule {
            conclusion_code: ARCHSIG_TWO_PROFILES_REPORTED_SEPARATELY,
            theorem_ref: None,
            principal_text: "Two selected measurement profiles are reported separately because their comparison contract does not establish a shared class reading.",
            boundary: "Derive a selected coarse-to-fine relation from normalized ArchMap covers before reading a cross-profile class-zero relation.",
            generated_discipline: "generated separate-profile comparison record",
        },
        ARCHSIG_MEASURED_AG_OBSTRUCTION_UNDER_PROFILE => SummaryTranslationRule {
            conclusion_code: ARCHSIG_MEASURED_AG_OBSTRUCTION_UNDER_PROFILE,
            theorem_ref: None,
            principal_text: "ArchSig reports selected AG obstruction rows together with the assumption ledger entries that identify their theoremRef fields.",
            boundary: "Read the selected structural verdict, its dependsOnAssumptions refs, and the corresponding assumption ledger entries together.",
            generated_discipline: "generated profile-relative detection",
        },
        ARCHSIG_NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE => SummaryTranslationRule {
            conclusion_code: ARCHSIG_NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE,
            theorem_ref: Some("part4/12.3"),
            principal_text: "No selected H1 glue mismatch was measured under the profile.",
            boundary: "Supply a selected nonzero cocycle support or different profile before claiming an H1 obstruction.",
            generated_discipline: "generated Cech zero detection",
        },
        _ => SummaryTranslationRule {
            conclusion_code: ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE,
            theorem_ref: None,
            principal_text: "ArchSig produced a profile-relative foundation result with non-terminal rows still visible.",
            boundary: "Supply the missing evaluator support named by boundaryStatements before reading a terminal conclusion.",
            generated_discipline: "generated foundation readiness surface",
        },
    }
}

fn summary_translation_rule_json(rule: &SummaryTranslationRule) -> Value {
    json!({
        "conclusionCode": rule.conclusion_code,
        "theoremRef": rule.theorem_ref,
        "principalText": rule.principal_text,
        "boundary": rule.boundary,
        "generatedDiscipline": rule.generated_discipline,
        "supportDiscipline": "nonzero conclusions must name concrete selected support in active translationRule.concreteSupportRefs",
        "emitsLawSatisfiedWithoutLawCheck": false
    })
}

fn active_summary_translation_rule_json(
    rule: &SummaryTranslationRule,
    packet: &ArchSigMeasurementPacketV1,
) -> Value {
    let mut rule_json = summary_translation_rule_json(rule);
    rule_json["concreteSupportRefs"] = json!(summary_concrete_support_refs(packet, rule));
    rule_json
}

fn summary_concrete_support_refs(
    packet: &ArchSigMeasurementPacketV1,
    rule: &SummaryTranslationRule,
) -> Vec<String> {
    match rule.conclusion_code {
        ARCHSIG_SAGA_MEASURED_NONGLUING_RESIDUAL => {
            let mut refs = Vec::new();
            if let Some(residual_support) = packet
                .computed_invariants
                .iter()
                .find(|invariant| invariant["invariantId"] == "saga-descent:boundary-membership")
                .map(|invariant| &invariant["boundaryMembership"]["residualSupport"])
            {
                collect_json_string_leaves(residual_support, &mut refs);
            }
            refs
        }
        ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS => {
            let mut refs = Vec::new();
            if let Some(support) = packet
                .computed_invariants
                .iter()
                .find(|invariant| invariant["invariantId"] == "saga-descent:residual-class")
                .map(|invariant| &invariant["residualClassSupport"]["representative"])
            {
                collect_json_string_leaves(support, &mut refs);
            }
            refs
        }
        ARCHSIG_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE => packet
            .computed_invariants
            .iter()
            .find(|invariant| invariant["evaluator"] == "ag.cech-obstruction")
            .and_then(|invariant| invariant["classSupport"]["supportAtomRefs"].as_array())
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(str::to_string)
            .collect(),
        ARCHSIG_REPAIR_TARGETS_IDENTIFIED => packet
            .computed_invariants
            .iter()
            .find(|invariant| invariant["evaluator"] == "ag.square-free-repair")
            .and_then(|invariant| invariant["alexanderDualRepair"]["minimalHittingSets"].as_array())
            .into_iter()
            .flatten()
            .filter_map(|set| {
                set.as_array().map(|items| {
                    items
                        .iter()
                        .filter_map(Value::as_str)
                        .collect::<Vec<_>>()
                        .join("+")
                })
            })
            .collect(),
        ARCHSIG_MEASURED_AG_OBSTRUCTION_UNDER_PROFILE => {
            let mut refs = Vec::new();
            if let Some(invariant) = packet
                .computed_invariants
                .iter()
                .find(|invariant| invariant["evaluator"] == "ag.law-conflict-tor")
            {
                collect_json_string_leaves(&invariant["commonAmbient"]["sourceRefs"], &mut refs);
                if let Some(conflicts) = invariant["lawConflicts"].as_array() {
                    for conflict in conflicts {
                        collect_json_string_leaves(&conflict["sourceRefs"], &mut refs);
                        collect_json_string_leaves(&conflict["contextRefs"], &mut refs);
                    }
                }
            }
            refs.sort();
            refs.dedup();
            refs
        }
        _ => Vec::new(),
    }
}

fn collect_json_string_leaves(value: &Value, output: &mut Vec<String>) {
    match value {
        Value::String(text) => output.push(text.clone()),
        Value::Array(items) => {
            for item in items {
                collect_json_string_leaves(item, output);
            }
        }
        Value::Object(object) => {
            for item in object.values() {
                collect_json_string_leaves(item, output);
            }
        }
        _ => {}
    }
}

pub fn selected_measurement_profile_v1<'a>(
    policy: &LawPolicyDocumentV1,
    measurement_profiles: &'a BTreeMap<String, MeasurementProfileV1>,
) -> Option<&'a MeasurementProfileV1> {
    let profile_ref = policy.measurement_profile_ref.as_deref()?;
    measurement_profiles.get(profile_ref)
}

fn diagnostic_stage_rank(stage: &str) -> Option<u8> {
    match stage {
        "raw-values" => Some(0),
        "boundary-membership" => Some(1),
        "descent" => Some(2),
        "class-transfer" => Some(3),
        "law-grounded" => Some(4),
        _ => None,
    }
}

fn evaluator_stage_rank(evaluator: &str) -> u8 {
    match evaluator {
        "ag.saga-descent" => 2,
        "ag.saga-grounded" => 4,
        _ => 0,
    }
}

fn profile_with_law_surface_witnesses(
    policy: &LawPolicyDocumentV1,
    profile: &MeasurementProfileV1,
    law_surface: &LawEquationSurfaceV1,
) -> Result<MeasurementProfileV1, String> {
    let mut execution_profile = profile.clone();
    let mut witnesses = BTreeSet::new();
    for entry in policy.policies.iter().filter(|entry| {
        entry
            .evaluator
            .as_deref()
            .is_some_and(|evaluator| evaluator.starts_with("ag."))
    }) {
        let evaluator = entry.evaluator.as_deref().unwrap_or_default();
        let laws = if evaluator == "ag.law-conflict-tor" {
            resolve_tor_laws(Some(law_surface), entry.law_pair.as_deref(), evaluator)?
        } else {
            entry
                .law
                .as_deref()
                .and_then(|law_id| law_surface.laws.iter().find(|law| law.law_id == law_id))
                .into_iter()
                .collect::<Vec<_>>()
        };
        for law in laws {
            for witness in &law.witness_variables {
                witnesses.insert((evaluator.to_string(), witness.variable.clone()));
            }
        }
    }
    execution_profile.witness_family = witnesses
        .into_iter()
        .map(|(law, variable)| MeasurementProfileWitnessV1 { law, variable })
        .collect();
    Ok(execution_profile)
}

fn boundary_statements_for_measurement_packet(
    packet: &ArchSigMeasurementPacketV1,
) -> Vec<BoundaryStatementV1> {
    let mut statements = packet
        .non_conclusions
        .iter()
        .enumerate()
        .map(|(index, text)| BoundaryStatementV1 {
            id: format!("boundary:silence-by-design:{index}"),
            kind: "silence_by_design".to_string(),
            scope_refs: vec![packet.packet_id.clone()],
            reason: "compat_non_conclusion".to_string(),
            text: text.clone(),
        })
        .collect::<Vec<_>>();
    statements.extend(m8_silence_boundary_statements(packet));

    for (index, row) in packet.structural_verdict.iter().enumerate() {
        let scope_ref = structural_verdict_ref(row);
        if row.verdict == "not_computed"
            && row.evaluator == "ag.saga-descent"
            && row.law == "saga.residual-boundary-membership"
            && row.verdict_data.method_status == "residual_derivation_fault"
        {
            statements.push(BoundaryStatementV1 {
                id: format!("boundary:residual-derivation-fault:{index}"),
                kind: "blocked_method".to_string(),
                scope_refs: vec![scope_ref.clone()],
                reason: "residual_derivation_fault".to_string(),
                text: format!(
                    "SAGA residual derivation failed closed and no descent conclusion was computed: {}",
                    row.reason.as_deref().unwrap_or("unnamed derivation fault")
                ),
            });
        }
        if row.verdict == "unmeasured" {
            statements.push(BoundaryStatementV1 {
                id: format!("boundary:unmeasured-support:{index}"),
                kind: "unmeasured_support".to_string(),
                scope_refs: vec![scope_ref.clone()],
                reason: row.verdict_data.method_status.clone(),
                text: row.reason.clone().unwrap_or_else(|| {
                    "Unmeasured structural verdict is not a measured zero result.".to_string()
                }),
            });
        }
        if row.verdict == "not_computed"
            && row.verdict_data.method_status == "sections_not_observed"
        {
            statements.push(BoundaryStatementV1 {
                id: format!("boundary:silence-by-design:cech-sections-not-observed:{index}"),
                kind: "silence_by_design".to_string(),
                scope_refs: vec![scope_ref.clone()],
                reason: row.verdict_data.method_status.clone(),
                text: row.reason.clone().unwrap_or_else(|| {
                    "sections_not_observed: supply sectionValue observations on both endpoint contexts of a selected edge (or an explicit cocycleValue) before the H1 class can be measured".to_string()
                }),
            });
        } else if row.verdict == "not_computed"
            && row.verdict_data.method_status == "diagnostic_ceiling_not_reached"
        {
            statements.push(BoundaryStatementV1 {
                id: format!("boundary:silence-by-design:diagnostic-ceiling:{index}"),
                kind: "silence_by_design".to_string(),
                scope_refs: vec![scope_ref.clone()],
                reason: row.verdict_data.method_status.clone(),
                text: row.reason.clone().unwrap_or_else(|| {
                    "The selected diagnostic ceiling does not include this evaluator stage."
                        .to_string()
                }),
            });
        } else if row.verdict == "not_computed" {
            statements.push(BoundaryStatementV1 {
                id: format!("boundary:blocked-method:{index}"),
                kind: "blocked_method".to_string(),
                scope_refs: vec![scope_ref.clone()],
                reason: row.verdict_data.method_status.clone(),
                text: row.reason.clone().unwrap_or_else(|| {
                    "Structural verdict is not computed under the selected method.".to_string()
                }),
            });
        }
    }

    for (index, row) in packet.structural_verdict.iter().enumerate() {
        if row.evaluator != "ag.square-free-repair" {
            continue;
        }
        let scope_ref = structural_verdict_ref(row);
        let Some(invariant) = packet
            .computed_invariants
            .iter()
            .find(|invariant| invariant["evaluator"] == "ag.square-free-repair")
        else {
            continue;
        };
        for (generator_index, generator) in invariant["obstructionIdeal"]["generators"]
            .as_array()
            .into_iter()
            .flatten()
            .enumerate()
        {
            let has_support_atom_refs = generator["supportAtomRefs"]
                .as_array()
                .map(|refs| !refs.is_empty())
                .unwrap_or(false);
            if has_support_atom_refs {
                continue;
            }
            let generator_id = generator["generatorId"]
                .as_str()
                .unwrap_or("unknown-generator");
            let support = generator["support"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .collect::<Vec<_>>()
                .join(",");
            // Do not let one unobserved generator override a row-level
            // measured_nonzero result when another generator is observed. A
            // nonzero row uses the packet scope because the computed invariant
            // itself carries the measured support and cannot carry a silence
            // scope at the same time.
            let scope_refs = if row.verdict == "measured_zero" {
                vec![scope_ref.clone()]
            } else {
                vec![packet.packet_id.clone()]
            };
            statements.push(BoundaryStatementV1 {
                id: format!(
                    "boundary:silence-by-design:square-free:{index}:{generator_index}"
                ),
                kind: "silence_by_design".to_string(),
                scope_refs,
                reason: "declared_generator_unobserved".to_string(),
                text: format!(
                    "Declared square-free generator {generator_id} ({support}) has no selected support atom occurrence; its structural reading is silent under this measurement profile."
                ),
            });
        }
    }

    for (index, row) in packet.structural_verdict.iter().enumerate() {
        if row.evaluator != "ag.cech-obstruction"
            || !matches!(row.verdict.as_str(), "measured_zero" | "measured_nonzero")
        {
            continue;
        }
        let Some(invariant) = packet
            .computed_invariants
            .iter()
            .find(|invariant| invariant["evaluator"] == "ag.cech-obstruction")
        else {
            continue;
        };
        let unobserved_edges = invariant["unobservedEdgeRefs"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>();
        if unobserved_edges.is_empty() {
            continue;
        }
        // Follow the square-free precedent: qualify a measured_zero row with the
        // silence directly, but do not attach silence to a measured_nonzero row
        // (the nonzero result stands on its observed support). The invariant
        // itself has status "computed", so it cannot carry a silence scope.
        let scope_refs = if row.verdict == "measured_zero" {
            vec![structural_verdict_ref(row)]
        } else {
            vec![packet.packet_id.clone()]
        };
        statements.push(BoundaryStatementV1 {
            id: format!("boundary:silence-by-design:cech-unobserved-edges:{index}"),
            kind: "silence_by_design".to_string(),
            scope_refs,
            reason: "sections_not_observed_on_selected_edges".to_string(),
            text: format!(
                "The measured H1 class is restricted to observed edges; selected edges without section observations stay silent: {}. Supply sectionValue observations on both endpoint contexts (or an explicit cocycleValue) to include an edge.",
                unobserved_edges.join(", ")
            ),
        });
    }

    for (index, invariant) in packet.computed_invariants.iter().enumerate() {
        if invariant["invariantId"] != "saga-descent:class-vocabulary-boundary" {
            continue;
        }
        statements.push(BoundaryStatementV1 {
            id: format!("boundary:silence-by-design:saga-class-vocabulary:{index}"),
            kind: "silence_by_design".to_string(),
            scope_refs: vec![packet.packet_id.clone()],
            reason: "class_vocabulary_not_unlocked_without_declared_triples".to_string(),
            text: "The derived residual component has no triple faces, so the cocycle condition is not checked; the reading stays at selected 1-skeleton boundary membership and the class vocabulary is not unlocked.".to_string(),
        });
    }

    for (index, reading) in packet.analytic_readings.iter().enumerate() {
        if reading.evaluator == "ag.harmonic-debt"
            && reading.value["lowerBoundStatus"] == "cost_model_not_supplied"
        {
            statements.push(BoundaryStatementV1 {
                id: format!("boundary:silence-by-design:harmonic-debt-cost-model:{index}"),
                kind: "silence_by_design".to_string(),
                scope_refs: vec![reading.reading_id.clone()],
                reason: "cost_model_not_supplied".to_string(),
                text: "Supply analytic.costModel with a positive Lipschitz constant and harmonic resolution before reading essentialRepairLowerBound.".to_string(),
            });
        }
        if reading.regime.as_deref() == Some("theorem-candidate")
            && reading.structural_verdict_ref.is_none()
        {
            statements.push(BoundaryStatementV1 {
                id: format!("boundary:not-applicable:{index}"),
                kind: "not_applicable".to_string(),
                scope_refs: vec![reading.reading_id.clone()],
                reason: "analytic_only".to_string(),
                text: "Theorem-candidate reading is analytic-only and cannot generate a structural verdict.".to_string(),
            });
        }
    }

    for (index, invariant) in packet.computed_invariants.iter().enumerate() {
        if invariant["status"] == "silence_by_design" {
            let invariant_id = invariant["invariantId"]
                .as_str()
                .unwrap_or("unknown-invariant");
            let reason = invariant["reason"]
                .as_str()
                .unwrap_or("measurement_prerequisite_not_measured");
            let what_next = invariant["whatNext"].as_str().unwrap_or(
                "supply the missing measurement prerequisite before reading this invariant",
            );
            let boundary_id = format!(
                "boundary:silence-by-design:{}:{index}",
                measurement_ref_segment(invariant["evaluator"].as_str().unwrap_or("unknown"))
            );
            statements.push(BoundaryStatementV1 {
                id: boundary_id,
                kind: "silence_by_design".to_string(),
                scope_refs: vec![invariant_id.to_string()],
                reason: reason.to_string(),
                text: format!("{reason}: {what_next}"),
            });
        }
    }

    for (index, assumption) in packet.assumptions.iter().enumerate() {
        if assumption.status == "violated" {
            let assumption_id = assumption_id_for_schema(assumption);
            let mut scope_refs = vec![assumption_id.clone()];
            let mut dependent_scope_refs =
                dependent_blocked_measurement_scope_refs(packet, &assumption_id);
            if dependent_scope_refs.is_empty() {
                dependent_scope_refs = blocked_measurement_scope_refs(packet)
                    .into_iter()
                    .collect::<Vec<_>>();
            }
            scope_refs.extend(dependent_scope_refs);
            statements.push(BoundaryStatementV1 {
                id: format!("boundary:violated-assumption:{index}"),
                kind: "violated_assumption".to_string(),
                scope_refs,
                reason: assumption.status.clone(),
                text: format!(
                    "Assumption {} is violated for the selected measurement packet.",
                    assumption.theorem_ref
                ),
            });
        }
    }

    statements
}

fn m8_silence_boundary_statements(packet: &ArchSigMeasurementPacketV1) -> Vec<BoundaryStatementV1> {
    let mut statements = vec![BoundaryStatementV1 {
            id: "boundary:m8:higher-hn-silence".to_string(),
            kind: "silence_by_design".to_string(),
            scope_refs: vec![packet.packet_id.clone()],
            reason: "higher_hn_n_ge_3_part_iv_scope_boundary".to_string(),
            text: "Cohomological readings in degrees n>=3 are silent by design in this finite AG measurement packet: they are a Part IV scope boundary, not a measured zero result or a remaining task.".to_string(),
        }];
    if packet.profile.coefficient == "F2" {
        statements.push(BoundaryStatementV1 {
            id: "boundary:m8:non-abelian-stack-gerbe-vocabulary".to_string(),
            kind: "out_of_selected_vocabulary".to_string(),
            scope_refs: vec![packet.packet_id.clone()],
            reason: "non_abelian_stack_gerbe_outside_abelian_f2_vocabulary".to_string(),
            text: "Non-abelian stack/gerbe degree-2 descent data is outside the selected banded abelian F2 vocabulary; banding-violated inputs remain outside this measurement lens.".to_string(),
        });
    }
    statements.push(BoundaryStatementV1 {
            id: "boundary:m8:higher-tor-unmeasured-support".to_string(),
            kind: "unmeasured_support".to_string(),
            scope_refs: vec![packet.packet_id.clone()],
            reason: "higher_tor_i_ge_2_unmeasured_support".to_string(),
            text: "Higher Tor_i for i>=2 remains unmeasured support: degree-1 Tor_1 readings do not discharge derived transversality or all higher Tor vanishing.".to_string(),
        });
    statements
}

fn assumption_theorem_refs(assumptions: &[AgAssumptionLedgerEntryV1]) -> Vec<String> {
    assumptions
        .iter()
        .map(assumption_id_for_schema)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn is_measured_verdict(verdict: &str) -> bool {
    matches!(verdict, "measured_zero" | "measured_nonzero")
}

fn apply_assumption_dependency_propagation(packet: &mut ArchSigMeasurementPacketV1) {
    let violated = packet
        .assumptions
        .iter()
        .filter(|assumption| assumption.status == "violated")
        .map(assumption_id_for_schema)
        .collect::<BTreeSet<_>>();
    if violated.is_empty() {
        return;
    }

    for row in &mut packet.structural_verdict {
        if !is_measured_verdict(&row.verdict) {
            continue;
        }
        let violated_dependencies = row
            .depends_on_assumptions
            .iter()
            .filter(|theorem_ref| violated.contains(*theorem_ref))
            .cloned()
            .collect::<Vec<_>>();
        if violated_dependencies.is_empty() {
            continue;
        }

        row.verdict = "not_computed".to_string();
        row.verdict_data.zero = false;
        row.verdict_data.non_zero = false;
        row.verdict_data.method_status = "depends_on_violated_assumption".to_string();
        row.verdict_data.cert_ref = None;
        row.reason = Some(format!(
            "depends_on violated {}",
            violated_dependencies.join(",")
        ));
    }
}

fn refresh_observation_evidence(
    packet: &mut ArchSigMeasurementPacketV1,
    normalized: &NormalizedArchMapV2,
) {
    let invariant_refs = packet
        .structural_verdict
        .iter()
        .map(|row| {
            generated_invariant_refs_for_row(row, &packet.computed_invariants, &packet.profile)
        })
        .collect::<Vec<_>>();
    let source_refs = packet
        .structural_verdict
        .iter()
        .map(|row| {
            generated_observation_source_refs_for_row(
                normalized,
                row,
                &packet.profile,
                &packet.computed_invariants,
            )
        })
        .collect::<Vec<_>>();
    let scope_sizes = packet
        .structural_verdict
        .iter()
        .map(|row| {
            generated_observation_scope_size(
                row,
                normalized,
                &packet.profile,
                &packet.computed_invariants,
            )
        })
        .collect::<Vec<_>>();
    packet.observation_invariant_refs = invariant_refs;
    packet.observation_source_refs = source_refs;
    packet.observation_scope_sizes = scope_sizes;
}
