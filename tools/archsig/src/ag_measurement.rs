use std::collections::{BTreeMap, BTreeSet};

use serde::Deserialize;
use serde_json::{Value, json};

use crate::law_execution::{LawExecutionPlanV1, build_law_execution_plan};
use crate::saga::{evaluate_saga_descent_v1, evaluate_saga_grounded_v1};
use crate::validation::{generic_validation_example, validation_check};
use crate::{
    ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE, ARCHSIG_ANALYSIS_CONCLUSION_CODES,
    ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION,
    ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION, ARCHSIG_MEASURED_AG_OBSTRUCTION_UNDER_PROFILE,
    ARCHSIG_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE, ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS,
    ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA, ARCHSIG_NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE,
    ARCHSIG_REPAIR_TARGETS_IDENTIFIED, ARCHSIG_SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA,
    ARCHSIG_SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS,
    ARCHSIG_SAGA_MEASURED_NONGLUING_RESIDUAL, ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX,
    ARCHSIG_TWO_PROFILES_REPORTED_SEPARATELY, ARCHSIG_VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR,
    AgAnalyticReadingV1, AgAssumptionLedgerEntryV1, AgStructuralVerdictV1, AgVerdictDataV1,
    ArchMapDocumentV2, ArchSigMeasurementPacketV1, BoundaryStatementV1, LawEquationSurfaceV1,
    LawPolicyDocumentV1, MeasurementProfileV1, MeasurementProfileWitnessV1, NormalizedArchMapV2,
    NormalizedAtomV2, NormalizedContextV2, NormalizedCoverV2, RepairPlanDocumentV1,
    SuppliedDataLedgerEntryV1, ValidationCheck, ValidationExample, analytic_claim_status,
    analytic_fidelity, assumption_id_for_schema,
};

const VERDICTS: [&str; 5] = [
    "measured_zero",
    "measured_nonzero",
    "unmeasured",
    "unknown",
    "not_computed",
];
const STRUCTURAL_VERDICT_EVALUATORS: [&str; 12] = [
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
    "ag.saga-comparison",
    "ag.saga-grounded",
];
const COMPUTED_INVARIANT_KINDS: [&str; 19] = [
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
    "h1-comparison-transfer",
    "saga-grounded-conclusions",
    "harmonic-debt",
];
const COMPUTED_INVARIANT_KIND_OWNERS: [(&str, &str); 1] =
    [("h1-comparison-transfer", "ag.saga-comparison")];
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

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SagaPresentationGeneratedEvidenceV1 {
    kind: String,
    presentation_exactness: bool,
    generator_completeness: bool,
    generated_cochain_map: SagaGeneratedCochainMapEvidenceV1,
    equation_residual: SagaEquationResidualEvidenceV1,
    semantic_residual: SagaSemanticResidualEvidenceV1,
    residual_witness: Option<SagaResidualWitnessEvidenceV1>,
    restriction_naturality: bool,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SagaGeneratedCochainMapEvidenceV1 {
    kind: String,
    degree_zero: Vec<SagaDerivedCellEvidenceV1>,
    degree_one: Vec<SagaDerivedCellEvidenceV1>,
    degree_two: Vec<SagaDerivedCellEvidenceV1>,
    degree_zero_commutative: bool,
    degree_one_commutative: bool,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SagaDerivedCellEvidenceV1 {
    cell_ref: String,
    local_phi_derived_from: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SagaEquationResidualEvidenceV1 {
    kind: String,
    target_cocycle: bool,
    #[serde(rename = "targetClassNonZero")]
    target_class_nonzero: Option<bool>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SagaSemanticResidualEvidenceV1 {
    kind: String,
    source_cocycle: bool,
    #[serde(rename = "sourceClassNonZero")]
    source_class_nonzero: Option<bool>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SagaResidualWitnessEvidenceV1 {
    kind: String,
    equation: String,
    source_image: Vec<SagaEquationCochainEvidenceV1>,
    equation_residual: Vec<SagaEquationCochainEvidenceV1>,
    h: Vec<SagaEquationChartAssignmentEvidenceV1>,
    difference_is_delta_zero: bool,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SagaEquationCochainEvidenceV1 {
    overlap_ref: String,
    equation_generators: Vec<String>,
    coefficients: Vec<u8>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SagaEquationChartAssignmentEvidenceV1 {
    chart_ref: String,
    equation_generators: Vec<String>,
    coefficients: Vec<u8>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SagaGeneratedQuotientTransferEvidenceV1 {
    level: String,
    kind: String,
    preserves_zero_predicate: bool,
    #[serde(rename = "sourceClassNonZero")]
    source_class_nonzero: bool,
    #[serde(rename = "targetClassNonZero")]
    target_class_nonzero: bool,
    source_invariant: String,
    target_invariant: String,
}

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
            theorem_ref: Some("part10/3.4"),
            principal_text: "The selected SAGA residual is measured outside B1 with concrete residual support; complete-support faithfulness is reported separately.",
            boundary: "Supply a different complete-support residual or Stage 2 comparison data before claiming repair gluing.",
            generated_discipline: "generated complete-support boundary-membership detection",
        },
        ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX => SummaryTranslationRule {
            conclusion_code: ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX,
            theorem_ref: Some("part10/3.5"),
            principal_text: "The selected SAGA residual is measured inside B1 and the selected residual component is covered and faithful.",
            boundary: "Supply Stage 2 law surface and comparison artifacts before claiming global semantic repair.",
            generated_discipline: "generated complete-support boundary-membership detection",
        },
        ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS => SummaryTranslationRule {
            conclusion_code: ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS,
            theorem_ref: Some("part10/4.5"),
            principal_text: "The selected supplied finite complex contains a measured non-gluing residual class in Z1/B1.",
            boundary: "The class reading is relative to the supplied triple overlaps, additive coefficient, sheaf certificate, and gluing data.",
            generated_discipline: "generated supplied class representative detection",
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
        ARCHSIG_VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR => SummaryTranslationRule {
            conclusion_code: ARCHSIG_VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR,
            theorem_ref: Some("part8/7.3"),
            principal_text: "An existing verdict row is transported under the supplied refactor morphism compatibility contract.",
            boundary: "Supply the validated refactor-morphism artifact and matching witness again before reading transport.",
            generated_discipline: "generated declared refactor transport reading",
        },
        ARCHSIG_TWO_PROFILES_REPORTED_SEPARATELY => SummaryTranslationRule {
            conclusion_code: ARCHSIG_TWO_PROFILES_REPORTED_SEPARATELY,
            theorem_ref: None,
            principal_text: "Two selected measurement profiles are reported separately because their comparison contract does not establish a shared class reading.",
            boundary: "Supply a validated comparison or refinement artifact before reading a cross-profile transport.",
            generated_discipline: "generated separate-profile comparison record",
        },
        ARCHSIG_MEASURED_AG_OBSTRUCTION_UNDER_PROFILE => SummaryTranslationRule {
            conclusion_code: ARCHSIG_MEASURED_AG_OBSTRUCTION_UNDER_PROFILE,
            theorem_ref: None,
            principal_text: "Review the theoremRef-bearing structural verdict rows before reading any selected AG obstruction claim.",
            boundary: "Supply the relevant theoremRef-bearing evaluator row before reading this as a proved theorem attribution.",
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
        "ag.saga-comparison" => 3,
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
        if row.verdict == "unmeasured"
            && row.evaluator == "ag.saga-descent"
            && row.law == "saga.global-coherence"
            && row.verdict_data.method_status == "complete_support_not_declared"
        {
            statements.push(BoundaryStatementV1 {
                id: format!("boundary:silence-by-design:saga-global-coherence:{index}"),
                kind: "silence_by_design".to_string(),
                scope_refs: vec![scope_ref.clone()],
                reason: row.verdict_data.method_status.clone(),
                text: row.reason.clone().unwrap_or_else(|| {
                    "complete-support declaration or Stage 2 faithfulness data is required before global coherence can be stated".to_string()
                }),
            });
        } else if row.verdict == "unmeasured" {
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
            && row.evaluator == "ag.saga-descent"
            && row.verdict_data.method_status == "repair_plan_not_supplied"
        {
            statements.push(BoundaryStatementV1 {
                id: format!("boundary:silence-by-design:saga-descent:{index}"),
                kind: "silence_by_design".to_string(),
                scope_refs: vec![scope_ref.clone()],
                reason: row.verdict_data.method_status.clone(),
                text: row.reason.clone().unwrap_or_else(|| {
                    "ag.saga-descent is silent until a checked repair-plan artifact is supplied."
                        .to_string()
                }),
            });
        } else if row.verdict == "not_computed"
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
        let invariant_ref = invariant["invariantId"].as_str();
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
            // measured_nonzero result when another generator is observed.
            let mut scope_refs = Vec::new();
            if row.verdict == "measured_zero" {
                scope_refs.push(scope_ref.clone());
            }
            if let Some(invariant_ref) = invariant_ref {
                scope_refs.push(invariant_ref.to_string());
            }
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
            let boundary_id = if invariant["evaluator"] == "ag.saga-comparison" {
                format!("boundary:silence-by-design:saga-comparison:{index}")
            } else {
                format!(
                    "boundary:silence-by-design:{}:{index}",
                    measurement_ref_segment(invariant["evaluator"].as_str().unwrap_or("unknown"))
                )
            };
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

pub fn build_foundation_measurement_packet_v1(
    normalized: &NormalizedArchMapV2,
    archmap: &ArchMapDocumentV2,
    policy: &LawPolicyDocumentV1,
    law_surface: Option<&LawEquationSurfaceV1>,
    measurement_profiles: &BTreeMap<String, MeasurementProfileV1>,
    repair_plan: Option<&RepairPlanDocumentV1>,
    archmap_ref: &str,
    law_policy_ref: &str,
    law_surface_ref: Option<&str>,
    measurement_profile_ref: &str,
    repair_plan_ref: Option<&str>,
    residual_packet_ref: Option<&str>,
    refactor_morphism: Option<&Value>,
) -> Result<ArchSigMeasurementPacketV1, String> {
    if policy.policies.iter().any(|entry| entry.pack.is_some()) {
        return Err(
            "Stage 1 measurement packet builder rejects retired LawPolicy pack selectors; use explicit law/evaluator entries"
                .to_string(),
        );
    }
    let selected_profile = selected_measurement_profile_v1(policy, measurement_profiles)
        .ok_or_else(|| "AG measurement packet requires measurementProfileRef".to_string())?
        .clone();
    let law_surface = law_surface.ok_or_else(|| {
        "AG measurement packet requires --law-surface; witness variables are supplied only by the law surface".to_string()
    })?;
    let law_policy_report = crate::validate_law_policy_v1_report_with_profiles(
        policy,
        law_policy_ref,
        measurement_profiles,
        Some(law_surface),
    );
    if law_policy_report.summary.result == "fail" {
        return Err(
            "AG measurement packet requires a law-policy selector that passes validation"
                .to_string(),
        );
    }
    let profile = profile_with_law_surface_witnesses(policy, &selected_profile, law_surface)?;
    let stage3_examples =
        crate::validate_law_surface_stage3_against_archmap_v1(law_surface, &profile, normalized);
    if !stage3_examples.is_empty() {
        return Err(format!(
            "law-equation-surface Stage 3 contract failed: {}",
            stage3_examples
                .iter()
                .map(|example| {
                    format!(
                        "{}={}",
                        example.source.as_deref().unwrap_or("unknown"),
                        example.target.as_deref().unwrap_or("invalid")
                    )
                })
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    validate_profile_refs(&profile, normalized)?;
    for candidate in measurement_profiles.values() {
        validate_profile_refs(candidate, normalized)?;
        if candidate.site_ref != selected_profile.site_ref
            || candidate.cover_ref != selected_profile.cover_ref
        {
            return Err(format!(
                "measurement profiles {} and {} must have matching normalized site/cover refs",
                selected_profile.profile_id, candidate.profile_id
            ));
        }
    }
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
        evaluator: "ag.foundation".to_string(),
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
            checked_by: Some("archmap-schema052-validation.contexts-finite".to_string()),
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
        let entry_profile = entry
            .profile_ref
            .as_deref()
            .and_then(|profile_ref| measurement_profiles.get(profile_ref))
            .unwrap_or(&selected_profile);
        let profile = profile_with_law_surface_witnesses(policy, entry_profile, law_surface)?;
        validate_profile_refs(&profile, normalized)?;
        if let Some(ceiling) = profile
            .diagnostic_ceiling
            .as_ref()
            .and_then(|value| value.as_ref())
            .and_then(Value::as_str)
        {
            if diagnostic_stage_rank(ceiling)
                .is_some_and(|ceiling_rank| evaluator_stage_rank(evaluator) > ceiling_rank)
            {
                let method_status = "diagnostic_ceiling_not_reached";
                computed_invariants.push(json!({
                    "invariantId": format!("diagnostic-ceiling:{evaluator}:{}", profile.profile_id),
                    "evaluator": evaluator,
                    "status": "not_computed",
                    "methodStatus": method_status,
                    "diagnosticCeiling": ceiling,
                    "reason": format!("{evaluator} is above the declared diagnostic ceiling {ceiling}")
                }));
                structural_verdict.push(AgStructuralVerdictV1 {
                    evaluator: evaluator.to_string(),
                    law: entry.law.clone().unwrap_or_else(|| evaluator.to_string()),
                    verdict: "not_computed".to_string(),
                    verdict_data: AgVerdictDataV1 {
                        in_scope: true,
                        zero: false,
                        non_zero: false,
                        method_status: method_status.to_string(),
                        cert_ref: None,
                    },
                    depends_on_assumptions: Vec::new(),
                    reason: Some(format!(
                        "{evaluator} is above the declared diagnostic ceiling {ceiling}; the evaluator remains silent by design"
                    )),
                });
                continue;
            }
        }
        let selected_contexts_for_plan = (evaluator == "ag.cech-obstruction").then(|| {
            selected_cover_contexts(normalized, &profile)
                .into_iter()
                .collect::<BTreeSet<_>>()
        });
        let execution_plan = build_law_execution_plan(
            normalized,
            Some(law_surface),
            entry.law.as_deref(),
            evaluator,
            selected_contexts_for_plan.as_ref(),
        )?;
        if evaluator == "ag.cech-obstruction" {
            validate_cech_profile_v1(&profile)?;
            let measurement =
                evaluate_cech_obstruction_v1(normalized, &profile, execution_plan.as_ref());
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.cech-obstruction".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.coherence-obstruction" {
            validate_coherence_profile_v1(&profile)?;
            let measurement = evaluate_coherence_obstruction_v1(normalized, &profile);
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.coherence-obstruction".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.restriction-compatibility" {
            validate_restriction_profile_v1(&profile)?;
            let measurement = evaluate_restriction_compatibility_v1(normalized, &profile)?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.restriction-compatibility".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.section-factorization" {
            validate_section_profile_v1(&profile)?;
            let measurement =
                evaluate_section_factorization_v1(normalized, &profile, execution_plan.as_ref())?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.section-factorization".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.boundary-residue" {
            validate_boundary_residue_profile_v1(&profile)?;
            let measurement = evaluate_boundary_residue_v1(normalized, &profile)?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.boundary-residue".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.square-free-repair" {
            let law_id = entry.law.as_deref().ok_or_else(|| {
                "ag.square-free-repair requires an explicit law selector".to_string()
            })?;
            let law = resolve_closed_law(Some(law_surface), law_id, evaluator)?;
            let (witness_variables, archmap_aliases, binding_axis, binding_predicate) =
                law_witness_bindings(law)?;
            validate_square_free_profile_v1(&profile, &witness_variables)?;
            let measurement = evaluate_square_free_repair_v1(
                normalized,
                &profile,
                law,
                &witness_variables,
                &archmap_aliases,
                &binding_axis,
                &binding_predicate,
            )?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry.law.clone().unwrap_or_else(|| law_id.to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.law-conflict-tor" {
            let tor_laws =
                resolve_tor_laws(Some(law_surface), entry.law_pair.as_deref(), evaluator)?;
            let witness_variables = merged_law_witness_bindings(&tor_laws)?;
            validate_tor_profile_v1(&profile, &witness_variables)?;
            let measurement =
                evaluate_law_conflict_tor_v1(normalized, &profile, &tor_laws, &witness_variables)?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
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
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.sheaf-laplacian" {
            validate_laplacian_profile_v1(&profile)?;
            let measurement = evaluate_sheaf_laplacian_v1(normalized, &profile)?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
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
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.harmonic-debt" {
            let measurement = evaluate_harmonic_debt_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
        } else if evaluator == "ag.period-stokes" {
            validate_period_profile_v1(&profile)?;
            let measurement = evaluate_period_stokes_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
        } else if evaluator == "ag.period-stokes-audit" {
            validate_period_audit_profile_v1(&profile)?;
            let measurement = evaluate_period_stokes_audit_v1(normalized, &profile)?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.period-stokes-audit".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.support-transfer" {
            validate_transfer_profile_v1(&profile)?;
            let measurement = evaluate_support_transfer_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
        } else if evaluator == "ag.saga-descent" {
            if let Some(plan) = repair_plan {
                let measurement = evaluate_saga_descent_v1(archmap, plan);
                computed_invariants.extend(measurement.computed_invariants);
                assumptions.extend(measurement.assumptions);
                structural_verdict.extend(measurement.structural_verdict);
            } else {
                computed_invariants.push(json!({
                    "invariantId": "saga-descent-stage1-input",
                    "evaluator": "ag.saga-descent",
                    "status": "not_computed",
                    "methodStatus": "repair_plan_not_supplied",
                    "repairPlanRef": null
                }));
                structural_verdict.push(AgStructuralVerdictV1 {
                    evaluator: evaluator.to_string(),
                    law: entry
                        .law
                        .clone()
                        .unwrap_or_else(|| "ag.saga-descent".to_string()),
                    verdict: "not_computed".to_string(),
                    verdict_data: AgVerdictDataV1 {
                        in_scope: true,
                        zero: false,
                        non_zero: false,
                        method_status: "repair_plan_not_supplied".to_string(),
                        cert_ref: None,
                    },
                    depends_on_assumptions: Vec::new(),
                    reason: Some(
                        "repair-plan not supplied; ag.saga-descent remains silent by design until --repair-plan is provided.".to_string(),
                    ),
                });
            }
        } else if evaluator == "ag.saga-grounded" {
            if let Some(plan) = repair_plan {
                if let Some(execution_plan) = execution_plan.as_ref() {
                    let measurement = evaluate_saga_grounded_v1(
                        archmap,
                        normalized,
                        &profile,
                        plan,
                        execution_plan,
                    );
                    computed_invariants.extend(measurement.computed_invariants);
                    assumptions.extend(measurement.assumptions);
                    structural_verdict.extend(measurement.structural_verdict);
                } else {
                    computed_invariants.push(json!({
                        "invariantId": "saga-generated-end-to-end-packet",
                        "kind": "saga-grounded-conclusions",
                        "evaluator": "ag.saga-grounded",
                        "status": "not_computed",
                        "methodStatus": "execution_plan_not_supplied"
                    }));
                    structural_verdict.push(AgStructuralVerdictV1 {
                        evaluator: evaluator.to_string(),
                        law: entry.law.clone().unwrap_or_else(|| evaluator.to_string()),
                        verdict: "not_computed".to_string(),
                        verdict_data: AgVerdictDataV1 {
                            in_scope: true,
                            zero: false,
                            non_zero: false,
                            method_status: "execution_plan_not_supplied".to_string(),
                            cert_ref: None,
                        },
                        depends_on_assumptions: Vec::new(),
                        reason: Some(
                            "ag.saga-grounded requires a Stage 3 law execution plan".to_string(),
                        ),
                    });
                }
            } else {
                computed_invariants.push(json!({
                    "invariantId": "saga-generated-end-to-end-packet",
                    "kind": "saga-grounded-conclusions",
                    "evaluator": "ag.saga-grounded",
                    "status": "not_computed",
                    "methodStatus": "repair_plan_not_supplied"
                }));
                structural_verdict.push(AgStructuralVerdictV1 {
                    evaluator: evaluator.to_string(),
                    law: entry.law.clone().unwrap_or_else(|| evaluator.to_string()),
                    verdict: "not_computed".to_string(),
                    verdict_data: AgVerdictDataV1 {
                        in_scope: true,
                        zero: false,
                        non_zero: false,
                        method_status: "repair_plan_not_supplied".to_string(),
                        cert_ref: None,
                    },
                    depends_on_assumptions: Vec::new(),
                    reason: Some(
                        "repair-plan not supplied; ag.saga-grounded remains silent by design"
                            .to_string(),
                    ),
                });
            }
        } else if evaluator == "ag.refactor-transport" {
            // Refactor transport is analytic-only and is emitted below only when
            // both the declared morphism and a matching ArchMap witness exist.
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
                depends_on_assumptions: Vec::new(),
                reason: Some(
                    "AG evaluator schema is registered; mathematical computation is implemented by follow-up evaluator issues".to_string(),
                ),
            });
        }
    }
    let selected_contexts = selected_cover_contexts(normalized, &profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    analytic_readings.extend(refactor_transport_readings(
        normalized,
        &profile,
        &selected_contexts,
        &structural_verdict,
        refactor_morphism,
    ));

    let mut non_conclusions = vec![
        format!(
            "ArchSig v0.5.4 foundation packet is computed from {archmap_ref} and {law_policy_ref}; it is not a Lean proof object."
        ),
        "Unmeasured AG evaluator rows are schema handoff rows, not measured zero.".to_string(),
        "Theorem-candidate readings are analytic-only and cannot generate structural verdicts."
            .to_string(),
    ];
    if let Some(ceiling) = profile
        .diagnostic_ceiling
        .as_ref()
        .and_then(|value| value.as_ref())
        .and_then(Value::as_str)
        .filter(|ceiling| *ceiling != "raw-values")
    {
        non_conclusions.push(format!(
            "silence_by_design: diagnostic ceiling {ceiling} is not reached by the foundation evaluator; supply the corresponding SAGA data before emitting that stage"
        ));
    }
    let mut packet = ArchSigMeasurementPacketV1 {
        schema: ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA.to_string(),
        packet_id: format!("measurement:{}", normalized.source_archmap_id),
        profile,
        profiles: (measurement_profiles.len() > 1)
            .then(|| measurement_profiles.values().cloned().collect())
            .unwrap_or_default(),
        structural_verdict,
        computed_invariants,
        analytic_readings,
        assumptions,
        supplied_data: supplied_data_ledger(
            archmap_ref,
            law_policy_ref,
            law_surface_ref,
            measurement_profile_ref,
            repair_plan_ref,
            residual_packet_ref,
        ),
        boundary_statements: Vec::new(),
        non_conclusions,
    };
    apply_assumption_dependency_propagation(&mut packet);
    packet.boundary_statements = boundary_statements_for_measurement_packet(&packet);
    Ok(packet)
}

fn supplied_data_ledger(
    archmap_ref: &str,
    law_policy_ref: &str,
    law_surface_ref: Option<&str>,
    measurement_profile_ref: &str,
    repair_plan_ref: Option<&str>,
    residual_packet_ref: Option<&str>,
) -> Vec<SuppliedDataLedgerEntryV1> {
    let mut entries = vec![
        supplied_data_entry(
            "supplied:archmap",
            "archmap",
            archmap_ref,
            "archmap/v0.5.4-validation",
            "validated",
        ),
        supplied_data_entry(
            "supplied:law-policy",
            "law-policy",
            law_policy_ref,
            "law-policy/v0.5.4-validation",
            "validated",
        ),
        supplied_data_entry(
            "supplied:measurement-profile",
            "measurement-profile",
            measurement_profile_ref,
            "measurement-profile/v0.5.4-validation",
            "validated",
        ),
    ];
    if let Some(law_surface_ref) = law_surface_ref {
        entries.push(supplied_data_entry(
            "supplied:law-surface",
            "law-equation-surface",
            law_surface_ref,
            "law-equation-surface/v0.5.4-validation",
            "validated",
        ));
    }
    if let Some(repair_plan_ref) = repair_plan_ref {
        entries.push(supplied_data_entry(
            "supplied:repair-plan",
            "repair-plan",
            repair_plan_ref,
            "repair-plan/v0.5.4-validation",
            "validated",
        ));
    }
    if let Some(residual_packet_ref) = residual_packet_ref {
        entries.push(supplied_data_entry(
            "supplied:residual-packet",
            "residual-packet",
            residual_packet_ref,
            "residual-packet/v0.5.4-validation",
            "validated",
        ));
    }
    entries
}

fn supplied_data_entry(
    supplied_id: &str,
    kind: &str,
    source_artifact_ref: &str,
    check_ref: &str,
    status: &str,
) -> SuppliedDataLedgerEntryV1 {
    SuppliedDataLedgerEntryV1 {
        supplied_id: supplied_id.to_string(),
        kind: kind.to_string(),
        source_artifact_ref: source_artifact_ref.to_string(),
        conformance: json!({
            "status": status,
            "checkRef": check_ref,
            "boundary": "validated CLI input artifact; semantic content beyond the selected contract remains outside the packet claim"
        }),
    }
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
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct CoherenceMeasurementV1 {
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
struct CoherenceFaceV1 {
    face_id: String,
    context_refs: Vec<String>,
    edge_refs: Vec<String>,
    shared_atom_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct CoherenceTetrahedronV1 {
    tetrahedron_id: String,
    context_refs: Vec<String>,
    face_refs: Vec<String>,
    shared_atom_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct CoherenceWitnessV1 {
    atom_ref: String,
    face_ref: String,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct SquareFreeGeneratorV1 {
    generator_id: String,
    support: Vec<String>,
    support_atom_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct RestrictionMeasurementV1 {
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
struct RestrictionGeneratorV1 {
    generator_id: String,
    context_ref: String,
    support: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct RestrictionEdgeCheckV1 {
    edge_ref: String,
    source_context: String,
    target_context: String,
    status: String,
    source_generators: Vec<RestrictionGeneratorV1>,
    target_generators: Vec<RestrictionGeneratorV1>,
    violations: Vec<RestrictionViolationV1>,
}

#[derive(Debug, Clone)]
struct RestrictionViolationV1 {
    generator_id: String,
    support: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct SectionMeasurementV1 {
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
struct SectionForbiddenSupportV1 {
    support_id: String,
    support: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct SectionAssignmentV1 {
    assignment_id: String,
    assigned: BTreeMap<String, bool>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct BoundaryResidueMeasurementV1 {
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
struct BoundaryResidueRoleV1 {
    atom_ref: String,
    context_ref: String,
    role: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct BoundaryResidueColumnV1 {
    column_id: String,
    source_context: String,
    boundary_context: String,
    support: Vec<String>,
    vector: Vec<u8>,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct BoundaryResidueMismatchV1 {
    atom_refs: Vec<String>,
    support: Vec<String>,
    vector: Vec<u8>,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
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
    analytic_readings: Vec<AgAnalyticReadingV1>,
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
    square_free: bool,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TorConflictClassV1 {
    conflict_id: String,
    degree: usize,
    support: Vec<String>,
    multidegree: Vec<String>,
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

struct HarmonicDebtMeasurementV1 {
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
struct PeriodAuditMeasurementV1 {
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
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
    support_targets: Vec<String>,
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

fn evaluate_coherence_obstruction_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> CoherenceMeasurementV1 {
    let selected_contexts = selected_cover_contexts(normalized, profile);
    let selected_context_set = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let mut assumptions = coherence_assumptions(profile, "checked");
    let max_coherence_contexts = profile
        .finite_bounds
        .max_coherence_contexts
        .min(MAX_COHERENCE_CONTEXTS);
    if selected_contexts.len() > max_coherence_contexts {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/10.1-selected-cover-budget".to_string(),
            assumption: format!(
                "selected cover has at most {max_coherence_contexts} contexts for finite H2 coherence enumeration"
            ),
            status: "violated".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
        return CoherenceMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "selected_cover_too_large".to_string(),
            cert_ref: None,
            reason: format!(
                "selected cover has {} contexts; ag.coherence-obstruction enumerates at most {max_coherence_contexts}",
                selected_contexts.len()
            ),
            computed_invariants: vec![coherence_invariant_json(
                profile,
                "not_computed",
                "selected_cover_too_large",
                &selected_contexts,
                &[],
                &[],
                &[],
                &[],
                &[],
                0,
                0,
                0,
                0,
                false,
                Vec::new(),
            )],
            assumptions,
        };
    }
    let edges = cech_edges(normalized, &selected_contexts);
    let faces = coherence_faces(normalized, &selected_contexts, &edges, &profile.cover_ref);
    let tetrahedra = coherence_tetrahedra(normalized, &selected_contexts, &faces);
    let witness_atoms = coherence_witness_atoms(normalized, &selected_context_set);

    if profile.coefficient != "F2" {
        assumptions = coherence_assumptions(profile, "violated");
        return CoherenceMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "banding_violated".to_string(),
            cert_ref: None,
            reason: "selected coefficient is outside the banded abelian F2 coherence vocabulary"
                .to_string(),
            computed_invariants: vec![coherence_invariant_json(
                profile,
                "not_computed",
                "banding_violated",
                &selected_contexts,
                &edges,
                &faces,
                &tetrahedra,
                &[],
                &[],
                0,
                0,
                0,
                0,
                false,
                Vec::new(),
            )],
            assumptions,
        };
    }

    if faces.is_empty() {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/10.1-empty-selected-2-skeleton".to_string(),
            assumption: "selected cover supplies a non-empty triple-overlap 2-skeleton".to_string(),
            status: "violated".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
        return CoherenceMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "empty_selected_2_skeleton".to_string(),
            cert_ref: None,
            reason: "selected cover has no triple-overlap 2-skeleton for ag.coherence-obstruction"
                .to_string(),
            computed_invariants: vec![coherence_invariant_json(
                profile,
                "not_computed",
                "empty_selected_2_skeleton",
                &selected_contexts,
                &edges,
                &faces,
                &tetrahedra,
                &[],
                &[],
                0,
                0,
                0,
                0,
                false,
                Vec::new(),
            )],
            assumptions,
        };
    }

    if faces.iter().any(|face| face.edge_refs.len() != 3) {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/10.1-incomplete-selected-2-skeleton".to_string(),
            assumption: "selected triple-overlap faces have all three restriction boundary edges"
                .to_string(),
            status: "violated".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
        return CoherenceMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "incomplete_selected_2_skeleton".to_string(),
            cert_ref: None,
            reason: "selected triple-overlap 2-skeleton is missing a boundary restriction edge"
                .to_string(),
            computed_invariants: vec![coherence_invariant_json(
                profile,
                "not_computed",
                "incomplete_selected_2_skeleton",
                &selected_contexts,
                &edges,
                &faces,
                &tetrahedra,
                &[],
                &[],
                0,
                0,
                0,
                0,
                false,
                Vec::new(),
            )],
            assumptions,
        };
    }

    if witness_atoms.is_empty() {
        return CoherenceMeasurementV1 {
            verdict: "unmeasured".to_string(),
            zero: false,
            non_zero: false,
            method_status: "coherence_witness_absent".to_string(),
            cert_ref: None,
            reason: "no coherence witness atom is supplied; H2 coherence remains silent"
                .to_string(),
            computed_invariants: vec![coherence_invariant_json(
                profile,
                "unmeasured",
                "coherence_witness_absent",
                &selected_contexts,
                &edges,
                &faces,
                &tetrahedra,
                &[],
                &[],
                0,
                0,
                0,
                0,
                false,
                Vec::new(),
            )],
            assumptions,
        };
    }

    let witnesses = coherence_witnesses_for_faces(&witness_atoms, &faces);
    let h = faces
        .iter()
        .map(|face| {
            (witnesses
                .iter()
                .filter(|witness| witness.face_ref == face.face_id)
                .count()
                % 2) as u8
        })
        .collect::<Vec<_>>();
    let d2_rows = coherence_d2_rows(&faces, &tetrahedra);
    let d2_h = d2_rows
        .iter()
        .map(|row| {
            row.iter()
                .zip(h.iter())
                .fold(0u8, |acc, (entry, value)| acc ^ (entry & value))
        })
        .collect::<Vec<_>>();
    let cocycle_gate_passed = d2_h.iter().all(|value| *value == 0);
    let d1_rows = coherence_d1_rows(&edges, &faces);
    let rank_d1 = matrix_rank_f2(d1_rows.clone());
    let rank_d2 = matrix_rank_f2(d2_rows.clone());
    let rank_ker_d2 = faces.len().saturating_sub(rank_d2);
    let h2_dimension = rank_ker_d2.saturating_sub(rank_d1);
    let selected_representative = cocycle_gate_passed
        .then(|| {
            if vector_in_span_f2(&d1_rows, &h) {
                h2_representative_f2(&d2_rows, &d1_rows, faces.len()).unwrap_or_default()
            } else {
                h.clone()
            }
        })
        .unwrap_or_default();
    let representative = coherence_representative_json(&selected_representative, &faces);

    let (verdict, zero, non_zero, method_status, reason) = if !cocycle_gate_passed {
        (
            "not_computed".to_string(),
            false,
            false,
            "not_2_cocycle".to_string(),
            "coherence 2-cochain fails the d2 h = 0 cocycle gate; im d1 membership is not evaluated".to_string(),
        )
    } else if h2_dimension == 0 {
        (
            "measured_zero".to_string(),
            true,
            false,
            "finite_f2_h2_coherence_computed".to_string(),
            "finite F2 H2 coherence quotient is zero on the selected cover".to_string(),
        )
    } else {
        (
            "measured_nonzero".to_string(),
            false,
            true,
            "finite_f2_h2_coherence_computed".to_string(),
            "finite F2 H2 coherence quotient is nonzero on the selected cover".to_string(),
        )
    };
    let cert_ref = (verdict != "not_computed").then(|| {
        format!(
            "computedInvariants/coherence-obstruction:{}",
            profile.profile_id
        )
    });

    CoherenceMeasurementV1 {
        verdict: verdict.to_string(),
        zero,
        non_zero,
        method_status: method_status.to_string(),
        cert_ref,
        reason,
        computed_invariants: vec![coherence_invariant_json(
            profile,
            if verdict == "not_computed" {
                "not_computed"
            } else {
                "computed"
            },
            &method_status,
            &selected_contexts,
            &edges,
            &faces,
            &tetrahedra,
            &witnesses,
            &h,
            rank_d1,
            rank_ker_d2,
            h2_dimension,
            d2_rows.len(),
            cocycle_gate_passed,
            representative,
        )],
        assumptions,
    }
}

fn resolve_closed_law<'a>(
    law_surface: Option<&'a LawEquationSurfaceV1>,
    law_id: &str,
    evaluator: &str,
) -> Result<&'a crate::LawEquationV1, String> {
    let surface = law_surface.ok_or_else(|| {
        format!(
            "{evaluator} requires --law-surface; no registry or MeasurementProfile fallback is permitted"
        )
    })?;
    let law = surface
        .laws
        .iter()
        .find(|law| law.law_id == law_id)
        .ok_or_else(|| {
            format!(
                "{evaluator} law {law_id} is not declared by supplied law surface {}",
                surface.id
            )
        })?;
    if law.condition_type != "closed-equational" {
        return Err(format!(
            "{evaluator} law {law_id} must be closed-equational, found {}",
            law.condition_type
        ));
    }
    Ok(law)
}

fn resolve_tor_laws<'a>(
    law_surface: Option<&'a LawEquationSurfaceV1>,
    law_pair: Option<&[String]>,
    evaluator: &str,
) -> Result<Vec<&'a crate::LawEquationV1>, String> {
    let surface = law_surface.ok_or_else(|| {
        format!(
            "{evaluator} requires --law-surface; no registry or MeasurementProfile fallback is permitted"
        )
    })?;
    let law_pair = law_pair.ok_or_else(|| {
        format!(
            "{evaluator} requires an explicit lawPair declaration; lawId naming conventions are not selectors"
        )
    })?;
    let unique_laws = law_pair.iter().collect::<BTreeSet<_>>();
    if law_pair.len() != 2 || unique_laws.len() != 2 {
        return Err(format!(
            "{evaluator} lawPair must contain exactly two distinct law ids"
        ));
    }
    let laws = law_pair
        .iter()
        .map(|law_id| resolve_closed_law(Some(surface), law_id, evaluator))
        .collect::<Result<Vec<_>, _>>()?;
    if laws.iter().any(|law| {
        law.witness_variables
            .iter()
            .any(|witness| witness.binding.axis.as_deref() != Some("square-free"))
    }) {
        return Err(format!(
            "{evaluator} lawPair declarations must use square-free witness bindings"
        ));
    }
    Ok(laws)
}

fn law_witness_bindings(
    law: &crate::LawEquationV1,
) -> Result<(Vec<String>, BTreeMap<String, String>, String, String), String> {
    let mut witness_variables = Vec::new();
    let mut archmap_aliases = BTreeMap::new();
    let mut binding_pairs = BTreeSet::new();
    for witness in &law.witness_variables {
        let variable = witness.variable.trim();
        if variable.is_empty() {
            return Err(format!(
                "law surface law {} contains an empty witness variable",
                law.law_id
            ));
        }
        let alias = witness
            .binding
            .archmap_variable
            .as_deref()
            .unwrap_or(variable)
            .trim();
        if alias.is_empty() {
            return Err(format!(
                "law surface law {} gives witness {variable} an empty ArchMap alias",
                law.law_id
            ));
        }
        let axis = witness.binding.axis.as_deref().ok_or_else(|| {
            format!(
                "law surface law {} gives witness {variable} no binding axis",
                law.law_id
            )
        })?;
        let predicate = witness.binding.predicate.as_deref().ok_or_else(|| {
            format!(
                "law surface law {} gives witness {variable} no binding predicate",
                law.law_id
            )
        })?;
        binding_pairs.insert((axis.to_string(), predicate.to_string()));
        if archmap_aliases
            .insert(variable.to_string(), alias.to_string())
            .is_some()
        {
            return Err(format!(
                "law surface law {} repeats witness variable {variable}",
                law.law_id
            ));
        }
        witness_variables.push(variable.to_string());
    }
    let mut binding_pairs = binding_pairs.into_iter();
    let (binding_axis, binding_predicate) = binding_pairs.next().ok_or_else(|| {
        format!(
            "law surface law {} must declare at least one witness binding",
            law.law_id
        )
    })?;
    if binding_pairs.next().is_some() {
        return Err(format!(
            "law surface law {} mixes binding axis/predicate pairs across witnesses",
            law.law_id
        ));
    }
    witness_variables.sort();
    Ok((
        witness_variables,
        archmap_aliases,
        binding_axis,
        binding_predicate,
    ))
}

fn merged_law_witness_bindings(laws: &[&crate::LawEquationV1]) -> Result<Vec<String>, String> {
    let mut witness_variables = BTreeSet::new();
    let mut archmap_aliases = BTreeMap::new();
    for law in laws {
        let (law_witnesses, law_aliases, _, _) = law_witness_bindings(law)?;
        witness_variables.extend(law_witnesses);
        for (variable, alias) in law_aliases {
            if let Some(previous) = archmap_aliases.insert(variable.clone(), alias.clone()) {
                if previous != alias {
                    return Err(format!(
                        "Tor law surface witness {variable} has conflicting ArchMap aliases {previous} and {alias}"
                    ));
                }
            }
        }
    }
    Ok(witness_variables.into_iter().collect())
}

fn declared_law_supports(
    law: &crate::LawEquationV1,
    witness_variables: &[String],
) -> Result<Vec<Vec<String>>, String> {
    let witness_set = witness_variables.iter().collect::<BTreeSet<_>>();
    let mut supports = Vec::new();
    for generator in &law.forbidden_support_generators {
        let mut support = generator.support.clone();
        support.sort();
        support.dedup();
        if support.is_empty()
            || support
                .iter()
                .any(|variable| !witness_set.contains(variable))
        {
            return Err(format!(
                "law surface law {} contains a forbidden support outside its declared witnesses",
                law.law_id
            ));
        }
        supports.push(support);
    }
    Ok(supports)
}

fn observed_support_matches(
    atom: &NormalizedAtomV2,
    support: &[String],
    archmap_aliases: &BTreeMap<String, String>,
    observed_axis: &str,
    observed_predicate: &str,
) -> bool {
    if atom.axis != observed_axis || atom.predicate != observed_predicate {
        return false;
    }
    let observed = square_free_atom_variables(atom)
        .into_iter()
        .collect::<BTreeSet<_>>();
    support.iter().all(|variable| {
        archmap_aliases
            .get(variable)
            .is_some_and(|alias| observed.contains(alias))
    })
}

fn observation_selector(
    evaluator_kind: &str,
    binding_axis: &str,
    binding_predicate: &str,
) -> Result<(&'static str, &'static str), String> {
    match evaluator_kind {
        "square-free" if binding_axis == "square-free" => {
            if matches!(binding_predicate, "support" | "cooccurrence") {
                Ok((
                    "square-free",
                    if binding_predicate == "support" {
                        "support"
                    } else {
                        "cooccurrence"
                    },
                ))
            } else {
                Err(format!(
                    "square-free law binding predicate {binding_predicate} is not an observed support predicate"
                ))
            }
        }
        "tor" if binding_axis == "square-free" => {
            if matches!(binding_predicate, "support" | "cooccurrence") {
                Ok(("tor", "lawIdealGenerator"))
            } else {
                Err(format!(
                    "Tor law binding predicate {binding_predicate} is not an accepted support predicate"
                ))
            }
        }
        _ => Err(format!(
            "{evaluator_kind} law binding axis/predicate {binding_axis}/{binding_predicate} is not executable"
        )),
    }
}

fn observed_tor_support_is_square_free(atom: &NormalizedAtomV2) -> bool {
    let raw_variables = atom
        .object
        .as_deref()
        .unwrap_or_default()
        .split(',')
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .collect::<Vec<_>>();
    raw_variables.len() == raw_variables.iter().collect::<BTreeSet<_>>().len()
}

fn evaluate_square_free_repair_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    law: &crate::LawEquationV1,
    witness_variables: &[String],
    archmap_aliases: &BTreeMap<String, String>,
    binding_axis: &str,
    binding_predicate: &str,
) -> Result<SquareFreeMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let generators = square_free_generators_from_law_surface(
        normalized,
        &selected_contexts,
        law,
        witness_variables,
        archmap_aliases,
        binding_axis,
        binding_predicate,
    )?;
    let minimal_forbidden_supports = minimal_supports(
        generators
            .iter()
            .map(|generator| generator.support.clone())
            .collect(),
    );
    let delta_faces =
        delta_faces_from_forbidden_supports(&witness_variables, &minimal_forbidden_supports);
    let delta_facets = maximal_faces(&delta_faces);
    let reduced_homology = reduced_simplicial_homology_f2(&delta_faces);
    let repair_hitting_sets = minimal_hitting_sets(&witness_variables, &minimal_forbidden_supports);
    let invariant_id = format!("square-free-repair:{}", profile.profile_id);
    let certificate = square_free_certificate(
        normalized,
        &selected_contexts,
        &minimal_forbidden_supports,
        &repair_hitting_sets,
        &generators,
        witness_variables.len(),
        &invariant_id,
    )?;
    let has_observed_support = generators
        .iter()
        .any(|generator| !generator.support_atom_refs.is_empty());
    let (verdict, zero, non_zero, method_status, cert_ref, reason) = if !has_observed_support {
        (
            "measured_zero".to_string(),
            true,
            false,
            "square_free_observation_empty".to_string(),
            certificate
                .as_ref()
                .map(|certificate| certificate.cert_ref.clone()),
            "no selected square-free support atom realizes any declared obstruction generator"
                .to_string(),
        )
    } else if let Some(certificate) = &certificate {
        if matches!(certificate.status.as_str(), "verified" | "computed") {
            (
                "measured_nonzero".to_string(),
                false,
                true,
                "nsdepth_certificate_computed".to_string(),
                Some(certificate.cert_ref.clone()),
                "observed square-free obstruction support was found and ArchSig computed the finite NSdepth certificate from the selected obstruction ideal".to_string(),
            )
        } else {
            (
                "measured_nonzero".to_string(),
                false,
                true,
                format!(
                    "observed_support_nsdepth_certificate_{}",
                    certificate.status
                ),
                Some(certificate.cert_ref.clone()),
                format!(
                    "observed square-free obstruction support was found; structural verdict follows observed support atoms while the NSdepth certificate is {}",
                    certificate.status
                ),
            )
        }
    } else {
        (
            "measured_nonzero".to_string(),
            false,
            true,
            "square_free_observed_support".to_string(),
            None,
            "observed square-free obstruction support was found; structural verdict follows observed support atoms even though the NSdepth certificate was not computed".to_string(),
        )
    };

    let computed_invariants = vec![
        json!({
            "invariantId": format!("square-free-repair:{}", profile.profile_id),
            "evaluator": "ag.square-free-repair",
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
            "minimalForbiddenSupports": minimal_forbidden_supports.clone(),
            "deltaComplex": {
                "id": "Delta_U",
                "faces": delta_faces,
                "reducedHomology": {
                    "field": "F2",
                    "method": "finite-f2-simplicial-boundary@1",
                    "betti": reduced_homology
                }
            },
            "alexanderDualRepair": {
                "minimalHittingSets": repair_hitting_sets.clone(),
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
                "effect": "NSdepth certificate is not computed; structural verdict follows observed support atom occurrence"
            }))
        }),
        lawful_locus_arrangement_invariant(
            profile,
            &witness_variables,
            &delta_facets,
            &minimal_forbidden_supports,
        ),
        delta_facet_link_reading_invariant(
            profile,
            &witness_variables,
            &delta_faces,
            &delta_facets,
        ),
    ];
    let analytic_readings = vec![AgAnalyticReadingV1 {
        reading_id: format!("theorem-candidate:repair-inspection:{}", profile.profile_id),
        evaluator: "ag.foundation".to_string(),
        value: json!({
            "readingKind": "repair-lower-bound-inspection@1",
            "selectedCoverRef": profile.cover_ref,
            "minimalForbiddenSupports": minimal_forbidden_supports,
            "minimalHittingSets": repair_hitting_sets,
            "lowerBoundSource": "alexanderDualRepair.minimalHittingSets",
            "nonClaim": "not automatic repair; not operation semantics",
            "reason": "repair inspection glyphs are viewer lower-bound markers grounded in the packet repair enumeration"
        }),
        regime: Some("theorem-candidate".to_string()),
        structural_verdict_ref: None,
    }];
    Ok(SquareFreeMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status,
        cert_ref,
        reason,
        computed_invariants,
        analytic_readings,
        assumptions: vec![
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/5.1".to_string(),
                assumption: "square-free witness variables selected by supplied law-equation-surface"
                    .to_string(),
                status: "checked".to_string(),
                checked_by: Some(format!(
                    "law-surface:provided-law-equation-surface"
                )),
                assumed_by: None,
            },
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/5.2".to_string(),
                assumption: "finite support family for Alexander dual enumeration".to_string(),
                status: "checked".to_string(),
                checked_by: Some("archmap-schema052-validation.contexts-finite".to_string()),
                assumed_by: None,
            },
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part3/7.2B".to_string(),
                assumption: "NSdepth certificate payload covers the computed square-free obstruction ideal within the selected witness family".to_string(),
                status: certificate
                    .as_ref()
                    .filter(|certificate| {
                        matches!(certificate.status.as_str(), "verified" | "computed")
                    })
                    .map(|_| "checked")
                    .unwrap_or("assumed")
                    .to_string(),
                checked_by: certificate
                    .as_ref()
                    .filter(|certificate| {
                        matches!(certificate.status.as_str(), "verified" | "computed")
                    })
                    .map(|certificate| format!("ag.square-free-repair:{}", certificate.cert_ref)),
                assumed_by: certificate
                    .as_ref()
                    .map(|certificate| {
                        if matches!(certificate.status.as_str(), "verified" | "computed") {
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

fn lawful_locus_arrangement_invariant(
    profile: &MeasurementProfileV1,
    witness_variables: &[String],
    facets: &[Vec<String>],
    minimal_forbidden_supports: &[Vec<String>],
) -> Value {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let components = facets
        .iter()
        .enumerate()
        .map(|(index, facet)| {
            let facet_set = facet.iter().cloned().collect::<BTreeSet<_>>();
            let vanishing_coords = witness_set
                .difference(&facet_set)
                .cloned()
                .collect::<Vec<_>>();
            json!({
                "componentId": format!("lawful-locus-component:{}", index + 1),
                "facet": facet,
                "vanishingCoords": vanishing_coords,
                "dimension": facet.len()
            })
        })
        .collect::<Vec<_>>();
    let dimension = facets.iter().map(Vec::len).max().unwrap_or(0);

    json!({
        "invariantId": format!("lawful-locus-arrangement:{}", profile.profile_id),
        "evaluator": "ag.square-free-repair",
        "method": "finite-delta-coordinate-arrangement@1",
        "claimScope": "selected cover and selected witness-family relative finite Delta_U coordinate arrangement",
        "selectedCoverRef": profile.cover_ref,
        "locusSymbol": "Flat_U(X)=V(I_Delta)",
        "witnessVariables": witness_variables,
        "minimalForbiddenSupports": minimal_forbidden_supports,
        "facets": facets,
        "components": components,
        "dimension": dimension,
        "irreducibleComponentCount": facets.len(),
        "nonConclusions": [
            "This invariant does not evaluate section-specific s^* I_Ob^U=0.",
            "The dimension is a finite coordinate-subspace arrangement dimension, not a total-correctness or runtime-safety claim.",
            "irreducibleComponentCount is not a safety score or structural verdict."
        ]
    })
}

fn delta_facet_link_reading_invariant(
    profile: &MeasurementProfileV1,
    witness_variables: &[String],
    delta_faces: &[Vec<String>],
    facets: &[Vec<String>],
) -> Value {
    let facet_dimensions = facets
        .iter()
        .enumerate()
        .map(|(index, facet)| {
            json!({
                "facetId": format!("delta-facet:{}", index + 1),
                "facet": facet,
                "dimension": facet.len()
            })
        })
        .collect::<Vec<_>>();
    let min_dimension = facets.iter().map(Vec::len).min().unwrap_or(0);
    let max_dimension = facets.iter().map(Vec::len).max().unwrap_or(0);
    let is_pure = facets
        .first()
        .is_none_or(|first| facets.iter().all(|facet| facet.len() == first.len()));
    let link_readings = witness_variables
        .iter()
        .map(|vertex| {
            let link_faces = delta_link_faces(delta_faces, vertex);
            json!({
                "vertex": vertex,
                "linkFaces": link_faces,
                "boundaryRanks": simplicial_boundary_rank_reading(&link_faces),
                "componentCount": simplicial_component_count(&link_faces)
            })
        })
        .collect::<Vec<_>>();
    let link_reduced_betti = witness_variables
        .iter()
        .map(|vertex| {
            let link_faces = delta_link_faces(delta_faces, vertex);
            json!({
                "vertex": vertex,
                "betti": reduced_simplicial_homology_f2(&link_faces)
            })
        })
        .collect::<Vec<_>>();

    json!({
        "invariantId": format!("delta-facet-link-reading:{}", profile.profile_id),
        "evaluator": "ag.square-free-repair",
        "method": "finite-delta-facet-link-neutral-reading@1",
        "claimScope": "selected cover and selected witness-family relative raw Delta_U combinatorial reading",
        "selectedCoverRef": profile.cover_ref,
        "facetDimensionReading": {
            "facets": facet_dimensions,
            "minDimension": min_dimension,
            "maxDimension": max_dimension
        },
        "linkBoundaryReading": link_readings,
        "linkReducedBetti": link_reduced_betti,
        "isPure": is_pure,
        "nonConclusions": [
            "This invariant reports raw selected Delta_U facet and link quantities only.",
            "linkBoundaryReading does not decide boundary-local lawfulness.",
            "isPure is not a safety score or structural verdict."
        ]
    })
}

fn maximal_faces(faces: &[Vec<String>]) -> Vec<Vec<String>> {
    let mut facets = faces
        .iter()
        .filter(|face| {
            !faces.iter().any(|candidate| {
                face.len() < candidate.len() && is_subset(face.as_slice(), candidate.as_slice())
            })
        })
        .cloned()
        .collect::<Vec<_>>();
    facets.sort();
    facets.dedup();
    facets
}

fn evaluate_restriction_compatibility_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<RestrictionMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile);
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let edges = cech_edges(normalized, &selected_contexts);
    let witness_variables = restriction_witness_variables(profile);
    let generators = restriction_generators(normalized, &selected, &witness_variables)?;
    let generators_by_context = generators.iter().cloned().fold(
        BTreeMap::<String, Vec<RestrictionGeneratorV1>>::new(),
        |mut acc, generator| {
            acc.entry(generator.context_ref.clone())
                .or_default()
                .push(generator);
            acc
        },
    );
    let missing_edges = edges.is_empty();
    let missing_generators = !missing_edges
        && edges.iter().any(|edge| {
            generators_by_context
                .get(&edge.source_context)
                .is_none_or(Vec::is_empty)
                || generators_by_context
                    .get(&edge.target_context)
                    .is_none_or(Vec::is_empty)
        });
    let method_status = if missing_edges {
        "empty_selected_restriction_edges"
    } else if missing_generators {
        "restriction_generator_missing"
    } else {
        "finite_support_inclusion_computed"
    };
    let edge_checks = if missing_edges {
        Vec::new()
    } else {
        edges
            .iter()
            .map(|edge| {
                let source_generators = generators_by_context
                    .get(&edge.source_context)
                    .cloned()
                    .unwrap_or_default();
                let target_generators = generators_by_context
                    .get(&edge.target_context)
                    .cloned()
                    .unwrap_or_default();
                let violations = if source_generators.is_empty() || target_generators.is_empty() {
                    Vec::new()
                } else {
                    source_generators
                        .iter()
                        .filter(|source| {
                            !target_generators
                                .iter()
                                .any(|target| is_subset(&target.support, &source.support))
                        })
                        .map(|source| RestrictionViolationV1 {
                            generator_id: source.generator_id.clone(),
                            support: source.support.clone(),
                            source_refs: source.source_refs.clone(),
                        })
                        .collect::<Vec<_>>()
                };
                RestrictionEdgeCheckV1 {
                    edge_ref: edge.edge_id.clone(),
                    source_context: edge.source_context.clone(),
                    target_context: edge.target_context.clone(),
                    status: if source_generators.is_empty() || target_generators.is_empty() {
                        "not_computed"
                    } else if violations.is_empty() {
                        "compatible"
                    } else {
                        "violated"
                    }
                    .to_string(),
                    source_generators,
                    target_generators,
                    violations,
                }
            })
            .collect::<Vec<_>>()
    };
    let violations = edge_checks
        .iter()
        .flat_map(|edge| edge.violations.iter())
        .collect::<Vec<_>>();
    let (verdict, zero, non_zero, reason) = if missing_edges {
        (
            "not_computed".to_string(),
            false,
            false,
            "selected cover has no restriction edges for ag.restriction-compatibility".to_string(),
        )
    } else if missing_generators {
        (
            "not_computed".to_string(),
            false,
            false,
            "selected restriction edge is missing source or target ideal generator contract"
                .to_string(),
        )
    } else if violations.is_empty() {
        (
            "measured_zero".to_string(),
            true,
            false,
            "all selected restriction edges satisfy finite monomial support inclusion".to_string(),
        )
    } else {
        (
            "measured_nonzero".to_string(),
            false,
            true,
            "some selected restriction edge does not carry source ideal generators into the target ideal; this may disappear under sheaf image redefinition and is not a defect of the theory object".to_string(),
        )
    };
    let cert_ref = matches!(verdict.as_str(), "measured_zero" | "measured_nonzero").then(|| {
        format!(
            "computedInvariants/restriction-compatibility:{}",
            profile.profile_id
        )
    });

    Ok(RestrictionMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status: method_status.to_string(),
        cert_ref,
        reason,
        computed_invariants: vec![restriction_invariant_json(
            profile,
            method_status,
            &selected_contexts,
            &edges,
            &witness_variables,
            &edge_checks,
        )],
        assumptions: restriction_assumptions(profile, method_status),
    })
}

fn evaluate_section_factorization_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    execution_plan: Option<&LawExecutionPlanV1>,
) -> Result<SectionMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let witness_variables = if let Some(plan) = execution_plan {
        plan.section_witness_variables.clone().ok_or_else(|| {
            "ag.section-factorization execution plan contains no witness variables".to_string()
        })?
    } else {
        section_witness_variables(profile)
    };
    let forbidden_supports = if let Some(plan) = execution_plan {
        section_forbidden_supports_from_plan(
            normalized,
            &selected_contexts,
            &witness_variables,
            plan,
        )?
    } else {
        section_forbidden_supports(normalized, &selected_contexts, &witness_variables)?
    };
    let minimal_forbidden_supports = minimal_section_forbidden_supports(&forbidden_supports);
    let assignment = section_assignment(normalized, &selected_contexts, &witness_variables)?;
    let assignment_status = if let Some(assignment) = &assignment {
        if assignment.assigned.len() == witness_variables.len() {
            "total"
        } else {
            "partial"
        }
    } else {
        "absent"
    };
    let active_support = assignment
        .as_ref()
        .map(|assignment| {
            assignment
                .assigned
                .iter()
                .filter_map(|(variable, value)| value.then_some(variable.clone()))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let violated_supports = if assignment.is_some() {
        minimal_forbidden_supports
            .iter()
            .filter(|support| {
                support.support.iter().all(|variable| {
                    let assignment_variable = execution_plan
                        .and_then(|plan| plan.section_variable_aliases.as_ref())
                        .and_then(|aliases| aliases.get(variable))
                        .unwrap_or(variable);
                    assignment
                        .as_ref()
                        .unwrap()
                        .assigned
                        .get(assignment_variable)
                        == Some(&true)
                })
            })
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    let method_status = if assignment.is_none() {
        "section_assignment_absent"
    } else if forbidden_supports.is_empty() {
        "obstruction_generators_absent"
    } else if !violated_supports.is_empty() || assignment_status == "total" {
        "finite_section_pullback_computed"
    } else {
        "section_assignment_partial_undecidable"
    };
    let (verdict, zero, non_zero, reason) = if assignment.is_none() {
        (
            "not_computed".to_string(),
            false,
            false,
            "selected section witnessAssignment atom is absent; ag.section-factorization remains silent".to_string(),
        )
    } else if forbidden_supports.is_empty() {
        (
            "not_computed".to_string(),
            false,
            false,
            "selected raw support atoms are absent; ArchSig does not infer an empty I_Ob^U presentation".to_string(),
        )
    } else if !violated_supports.is_empty() {
        (
            "measured_nonzero".to_string(),
            false,
            true,
            "selected section active support contains a minimal forbidden support, so s^* I_Ob^U is nonzero".to_string(),
        )
    } else if assignment_status == "total" {
        (
            "measured_zero".to_string(),
            true,
            false,
            "selected total Boolean section avoids all minimal forbidden supports, so s^* I_Ob^U=0 under the finite profile".to_string(),
        )
    } else {
        (
            "unknown".to_string(),
            false,
            false,
            "partial witnessAssignment does not yet decide whether activeSupport contains a minimal forbidden support".to_string(),
        )
    };
    let cert_ref = matches!(verdict.as_str(), "measured_zero" | "measured_nonzero").then(|| {
        format!(
            "computedInvariants/section-factorization:{}",
            profile.profile_id
        )
    });

    Ok(SectionMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status: method_status.to_string(),
        cert_ref,
        reason,
        computed_invariants: vec![section_invariant_json(
            profile,
            method_status,
            &witness_variables,
            &forbidden_supports,
            &minimal_forbidden_supports,
            assignment.as_ref(),
            assignment_status,
            &active_support,
            &violated_supports,
        )],
        assumptions: section_assumptions(profile, method_status, &forbidden_supports),
    })
}

fn evaluate_boundary_residue_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<BoundaryResidueMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let witness_variables = boundary_residue_witness_variables(profile);
    let roles = boundary_residue_roles(normalized, &selected_contexts)?;
    let role_map = boundary_residue_role_map(&roles);
    let roles_complete = boundary_residue_roles_complete(&roles, &selected_contexts);
    let (columns, mismatch) = if roles_complete {
        (
            boundary_residue_columns(
                normalized,
                &selected_contexts,
                &witness_variables,
                &role_map,
            )?,
            boundary_residue_mismatch(
                normalized,
                &selected_contexts,
                &witness_variables,
                &role_map,
            )?,
        )
    } else {
        (Vec::new(), None)
    };
    let coefficient_is_f2 = profile.coefficient == "F2";
    let method_status = if !roles_complete {
        "boundary_classification_absent"
    } else if mismatch.is_none() {
        "boundary_mismatch_section_absent"
    } else if columns.is_empty() {
        "boundary_restriction_matrix_absent"
    } else if coefficient_is_f2 {
        "finite_mayer_vietoris_d0_computed"
    } else {
        "finite_mayer_vietoris_d0_obstruction_only"
    };
    let image_membership = if matches!(
        method_status,
        "finite_mayer_vietoris_d0_computed" | "finite_mayer_vietoris_d0_obstruction_only"
    ) {
        mismatch.as_ref().map(|mismatch| {
            let rows = boundary_residue_matrix_rows(&columns, witness_variables.len());
            vector_in_span_f2(&rows, &mismatch.vector)
        })
    } else {
        None
    };
    let (verdict, zero, non_zero, reason) = match method_status {
        "boundary_classification_absent" => (
            "not_computed".to_string(),
            false,
            false,
            "selected cover lacks core / feature / boundary patch classification atoms for ag.boundary-residue".to_string(),
        ),
        "boundary_mismatch_section_absent" => (
            "not_computed".to_string(),
            false,
            false,
            "selected boundary mismatch section is absent; boundary residue remains silent".to_string(),
        ),
        "boundary_restriction_matrix_absent" => (
            "not_computed".to_string(),
            false,
            false,
            "selected core/feature to boundary restriction matrix columns are absent".to_string(),
        ),
        _ if image_membership == Some(true) && coefficient_is_f2 => (
            "measured_zero".to_string(),
            true,
            false,
            "boundary mismatch section lies in im(d^0), so the selected F2 boundary residue is absorbed".to_string(),
        ),
        _ if image_membership == Some(true) => (
            "unknown".to_string(),
            false,
            false,
            "F2 parity boundary residue lies in im(d^0), but non-F2 coefficient mode only supports one-way obstruction statements".to_string(),
        ),
        _ => (
            "measured_nonzero".to_string(),
            false,
            true,
            if coefficient_is_f2 {
                "boundary mismatch section is outside im(d^0), so the selected F2 boundary residue produces a global H1 class".to_string()
            } else {
                "boundary mismatch section is outside im(d^0) after F2 parity projection, yielding a one-way obstruction statement under the non-F2 coefficient profile".to_string()
            },
        ),
    };
    let cert_ref = matches!(verdict.as_str(), "measured_zero" | "measured_nonzero")
        .then(|| format!("computedInvariants/boundary-residue:{}", profile.profile_id));

    Ok(BoundaryResidueMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status: method_status.to_string(),
        cert_ref,
        reason,
        computed_invariants: vec![boundary_residue_invariant_json(
            profile,
            method_status,
            &witness_variables,
            &roles,
            &columns,
            mismatch.as_ref(),
            image_membership,
        )],
        assumptions: boundary_residue_assumptions(profile, method_status),
    })
}

fn evaluate_law_conflict_tor_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    laws: &[&crate::LawEquationV1],
    witness_variables: &[String],
) -> Result<TorMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
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
                "evaluator": "ag.law-conflict-tor",
                "method": "finite-monomial-tor-taylor@1",
                "selectedCoverRef": profile.cover_ref,
                "status": "not_computed",
                "reason": "no_common_ambient"
            })],
            analytic_readings: Vec::new(),
            assumptions: tor_assumptions(profile, None, "violated", "checked"),
        });
    };

    let generators = tor_ideal_generators(normalized, &selected_contexts, laws, witness_variables)?;
    let law_order = ambient.law_pair.clone();
    let selected_laws = generators
        .iter()
        .map(|generator| generator.law.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let ambient_laws = law_order.iter().cloned().collect::<BTreeSet<_>>();
    if selected_laws.is_empty() {
        let law_ideals = law_order
            .iter()
            .map(|law| {
                json!({
                    "law": law,
                    "generators": []
                })
            })
            .collect::<Vec<_>>();
        return Ok(TorMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "law_support_observation_incomplete".to_string(),
            cert_ref: None,
            reason: "no declared law support was observed in the selected common ambient"
                .to_string(),
            computed_invariants: vec![json!({
                "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
                "evaluator": "ag.law-conflict-tor",
                "method": "finite-monomial-tor-taylor@1",
                "claimScope": "degree-1 square-free monomial Tor over the selected common ambient pair",
                "resolution": profile.resolution_selector,
                "resolutionSelectorEffective": true,
                "selectedCoverRef": profile.cover_ref,
                "witnessVariables": witness_variables,
                "commonAmbient": {
                    "ambientRef": ambient.ambient_ref.clone(),
                    "atomRef": ambient.atom_ref.clone(),
                    "lawPair": ambient.law_pair.clone(),
                    "sourceRefs": ambient.source_refs.clone()
                },
                "lawIdeals": law_ideals,
                "lawConflicts": [],
                "torByDegree": [{
                    "degree": 1,
                    "classCount": null,
                    "status": "not_computed",
                    "coefficient": "F2",
                    "scope": "H_1 of Taylor(I_left) tensor R/I_right by square-free multidegree"
                }],
                "proxyComparison": {
                    "previousMethod": "finite-degree1-shared-support-conflict@1",
                    "proxyClassCount": 0,
                    "taylorClassCount": null,
                    "comparison": "not_computed"
                },
                "boundaryNote": "Taylor Tor_1 is a field-coefficient F2 reading over the selected common ambient; higher Tor_i and flat base change stability are not concluded."
            })],
            analytic_readings: Vec::new(),
            assumptions: tor_assumptions(profile, Some(&ambient), "violated", "checked"),
        });
    }
    let outside_ambient = selected_laws
        .iter()
        .filter(|law| !ambient_laws.contains(*law))
        .cloned()
        .collect::<Vec<_>>();
    if !outside_ambient.is_empty() {
        return Err(format!(
            "ag.law-conflict-tor selected law generators outside common ambient pair: {}",
            outside_ambient.join(",")
        ));
    }
    if selected_laws.len() != 2
        || selected_laws.iter().cloned().collect::<BTreeSet<_>>() != ambient_laws
    {
        return Ok(tor_partial_observation_measurement(
            profile,
            witness_variables,
            &ambient,
            &format!(
                "not every declared law support was observed in the selected common ambient: expected {}, observed {}",
                law_order.join(","),
                selected_laws.join(",")
            ),
        ));
    }
    let proxy_conflicts =
        tor_shared_support_proxy_classes(&generators, &law_order[0], &law_order[1]);
    let has_non_square_free = generators.iter().any(|generator| !generator.square_free);
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
                        "squareFree": generator.square_free,
                        "contextRefs": generator.context_refs,
                        "sourceRefs": generator.source_refs
                    }))
                    .collect::<Vec<_>>()
            })
        })
        .collect::<Vec<_>>();
    if has_non_square_free {
        return Ok(TorMeasurementV1 {
            verdict: "unmeasured".to_string(),
            zero: false,
            non_zero: false,
            method_status: "non_square_free_monomial".to_string(),
            cert_ref: Some(tor_certificate_ref(profile)),
            reason: "selected law ideal generator contains a non-square-free monomial; finite square-free Taylor regime is not measured".to_string(),
            computed_invariants: vec![json!({
                "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
                "evaluator": "ag.law-conflict-tor",
                "method": "finite-monomial-tor-taylor@1",
                "status": "unmeasured",
                "methodStatus": "non_square_free_monomial",
                "claimScope": "degree-1 square-free monomial Tor over the selected common ambient pair",
                "selectedCoverRef": profile.cover_ref,
                "resolutionSelector": profile.resolution_selector,
                "witnessVariables": witness_variables,
                "commonAmbient": {
                    "ambientRef": ambient.ambient_ref.clone(),
                    "atomRef": ambient.atom_ref.clone(),
                    "lawPair": ambient.law_pair.clone(),
                    "sourceRefs": ambient.source_refs.clone()
                },
                "lawIdeals": law_ideals,
                "lawConflicts": [],
                "torByDegree": [{
                    "degree": 1,
                    "classCount": Value::Null,
                    "coefficient": "F2",
                    "status": "unmeasured",
                    "reason": "non_square_free_monomial"
                }],
                "proxyComparison": {
                    "previousMethod": "finite-degree1-shared-support-conflict@1",
                    "proxyClassCount": proxy_conflicts.len(),
                    "taylorClassCount": Value::Null,
                    "comparison": "not_computed_outside_square_free_regime"
                },
                "boundaryNote": "Taylor Tor_1 is only measured for selected square-free monomial generators over F2; higher Tor_i and flat base change stability are not concluded."
            })],
            analytic_readings: Vec::new(),
            assumptions: tor_assumptions(profile, Some(&ambient), "checked", "violated"),
        });
    }

    let conflicts = tor_taylor_h1_classes(
        &generators,
        &law_order[0],
        &law_order[1],
        &witness_variables,
    );
    let has_conflict = !conflicts.is_empty();
    let conflict_json = conflicts
        .iter()
        .map(|conflict| {
            json!({
                "conflictId": conflict.conflict_id,
                "degree": conflict.degree,
                "support": conflict.support,
                "multidegree": conflict.multidegree,
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
        method_status: "finite_monomial_tor_taylor_computed".to_string(),
        cert_ref: Some(tor_certificate_ref(profile)),
        reason: if has_conflict {
            "finite monomial Taylor resolution found degree-1 Tor classes under the supplied common ambient"
                .to_string()
        } else {
            "finite monomial Taylor resolution found no degree-1 Tor class under the supplied common ambient"
                .to_string()
        },
        computed_invariants: vec![json!({
                "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
                "evaluator": "ag.law-conflict-tor",
                "method": "finite-monomial-tor-taylor@1",
                "claimScope": "degree-1 square-free monomial Tor over the selected common ambient pair",
                "resolution": profile.resolution_selector,
                "resolutionSelectorEffective": true,
            "selectedCoverRef": profile.cover_ref,
            "witnessVariables": witness_variables,
                "commonAmbient": {
                    "ambientRef": ambient.ambient_ref.clone(),
                    "atomRef": ambient.atom_ref.clone(),
                    "lawPair": ambient.law_pair.clone(),
                    "sourceRefs": ambient.source_refs.clone()
                },
            "lawIdeals": law_ideals,
            "lawConflicts": conflict_json,
            "torByDegree": [{
                "degree": 1,
                "classCount": conflicts.len(),
                "coefficient": "F2",
                "scope": "H_1 of Taylor(I_left) tensor R/I_right by square-free multidegree"
            }],
            "proxyComparison": {
                "previousMethod": "finite-degree1-shared-support-conflict@1",
                "proxyClassCount": proxy_conflicts.len(),
                "taylorClassCount": conflicts.len(),
                "comparison": if conflicts.len() <= proxy_conflicts.len() { "taylor_not_above_proxy" } else { "taylor_above_proxy" }
            },
            "boundaryNote": "Taylor Tor_1 is a field-coefficient F2 reading over the selected common ambient; higher Tor_i and flat base change stability are not concluded.",
            "nonConclusions": [
                "This evaluator computes only degree-1 monomial Taylor Tor over the selected square-free finite regime.",
                "Higher Tor_i for i>=2 remain outside this structural verdict.",
                "Flat base change stability is a theorem-candidate reading and is not concluded by this structural verdict."
            ]
        })],
        analytic_readings: vec![hilbert_interference_reading(profile, &ambient, &conflicts)],
        assumptions: tor_assumptions(profile, Some(&ambient), "checked", "checked"),
    })
}

fn tor_partial_observation_measurement(
    profile: &MeasurementProfileV1,
    witness_variables: &[String],
    ambient: &TorCommonAmbientV1,
    reason: &str,
) -> TorMeasurementV1 {
    let law_ideals = ambient
        .law_pair
        .iter()
        .map(|law| json!({"law": law, "generators": []}))
        .collect::<Vec<_>>();
    TorMeasurementV1 {
        verdict: "not_computed".to_string(),
        zero: false,
        non_zero: false,
        method_status: "law_support_observation_incomplete".to_string(),
        cert_ref: None,
        reason: reason.to_string(),
        computed_invariants: vec![json!({
            "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
            "evaluator": "ag.law-conflict-tor",
            "method": "finite-monomial-tor-taylor@1",
            "claimScope": "degree-1 square-free monomial Tor over the selected common ambient pair",
            "resolution": profile.resolution_selector,
            "resolutionSelectorEffective": true,
            "selectedCoverRef": profile.cover_ref,
            "witnessVariables": witness_variables,
            "commonAmbient": {
                "ambientRef": ambient.ambient_ref.clone(),
                "atomRef": ambient.atom_ref.clone(),
                "lawPair": ambient.law_pair.clone(),
                "sourceRefs": ambient.source_refs.clone()
            },
            "lawIdeals": law_ideals,
            "lawConflicts": [],
            "torByDegree": [{
                "degree": 1,
                "classCount": null,
                "status": "not_computed",
                "coefficient": "F2",
                "scope": "H_1 of Taylor(I_left) tensor R/I_right by square-free multidegree"
            }],
            "proxyComparison": {
                "previousMethod": "finite-degree1-shared-support-conflict@1",
                "proxyClassCount": 0,
                "taylorClassCount": null,
                "comparison": "not_computed"
            },
            "boundaryNote": "Taylor Tor_1 is a field-coefficient F2 reading over the selected common ambient; higher Tor_i and flat base change stability are not concluded."
        })],
        analytic_readings: Vec::new(),
        assumptions: tor_assumptions(profile, Some(ambient), "violated", "checked"),
    }
}

fn tor_certificate_ref(profile: &MeasurementProfileV1) -> String {
    format!("computedInvariants/law-conflict-tor:{}", profile.profile_id)
}

fn hilbert_interference_reading(
    profile: &MeasurementProfileV1,
    ambient: &TorCommonAmbientV1,
    conflicts: &[TorConflictClassV1],
) -> AgAnalyticReadingV1 {
    let mut by_degree = BTreeMap::<usize, usize>::new();
    for conflict in conflicts {
        *by_degree.entry(conflict.degree).or_default() += 1;
    }
    let series = by_degree
        .into_iter()
        .map(|(degree, coefficient)| {
            json!({
                "degree": degree,
                "coefficient": coefficient
            })
        })
        .collect::<Vec<_>>();

    AgAnalyticReadingV1 {
        reading_id: format!("analytic:hilbert-interference:{}", profile.profile_id),
        evaluator: "ag.law-conflict-tor".to_string(),
        value: json!({
            "readingKind": "hilbert-interference-series@1",
            "seriesSymbol": "Int_{U,V}(t)",
            "selectedCoverRef": profile.cover_ref.clone(),
            "lawPair": ambient.law_pair.clone(),
            "commonAmbientRef": ambient.ambient_ref.clone(),
            "regimeBoundary": "audit-only in the selected graded square-free monomial Taylor regime",
            "series": series,
            "sourceRefs": ambient.source_refs.clone(),
            "nonConclusion": "Hilbert interference is an audit reading only; it does not add or change structural verdicts"
        }),
        regime: Some("analytic-measurement".to_string()),
        structural_verdict_ref: None,
    }
}

fn principal_eigenvector_hotspots(matrix: &[Vec<f64>], cell_ids: &[String]) -> Vec<Value> {
    if matrix.is_empty() {
        return Vec::new();
    }
    let n = matrix.len();
    let mut vector = vec![1.0 / (n as f64).sqrt(); n];
    for _ in 0..32 {
        let mut next = vec![0.0; n];
        for (row_index, row) in matrix.iter().enumerate() {
            next[row_index] = row
                .iter()
                .zip(vector.iter())
                .map(|(entry, value)| entry.abs() * value)
                .sum::<f64>();
        }
        let norm = squared_norm(&next).sqrt();
        if norm <= 1.0e-12 {
            break;
        }
        for value in &mut next {
            *value /= norm;
        }
        vector = next;
    }
    let mut hotspots = cell_ids
        .iter()
        .zip(vector.iter())
        .map(|(cell, weight)| (cell.clone(), weight.abs()))
        .collect::<Vec<_>>();
    hotspots.sort_by(|left, right| {
        right
            .1
            .total_cmp(&left.1)
            .then_with(|| left.0.cmp(&right.0))
    });
    hotspots
        .into_iter()
        .map(|(cell, weight)| {
            json!({
                "cell": cell,
                "hotspotWeight": round_f64(weight)
            })
        })
        .collect()
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
                "evaluator": "ag.sheaf-laplacian",
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
                "ag.sheaf-laplacian boundary {} references cells outside selected cochain family",
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
    let curvature_hotspots = principal_eigenvector_hotspots(&laplacian, &cell_ids);
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
        "cells": cell_ids.clone(),
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
            "evaluator": "ag.sheaf-laplacian",
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
                evaluator: "ag.sheaf-laplacian".to_string(),
                value: analytic_value,
                regime: Some("analytic-measurement".to_string()),
                structural_verdict_ref: None,
            },
            AgAnalyticReadingV1 {
                reading_id: format!("theorem-candidate:harmonic-debt:{}", profile.profile_id),
                evaluator: "ag.foundation".to_string(),
                value: json!({
                    "readingKind": "harmonic-debt-minimality-candidate@1",
                    "essentialRepairLowerBound": round_f64(distance_to_flatness.sqrt()),
                    "reason": "harmonic debt minimality remains theorem-candidate and cannot generate a structural verdict"
                }),
                regime: Some("theorem-candidate".to_string()),
                structural_verdict_ref: None,
            },
            AgAnalyticReadingV1 {
                reading_id: format!("theorem-candidate:curvature-hotspot:{}", profile.profile_id),
                evaluator: "ag.foundation".to_string(),
                value: json!({
                    "readingKind": "curvature-transfer-perron-hotspot@1",
                    "sourceProxyReadingKind": "graph-laplacian-hodge-proxy@1",
                    "modelScope": "finite graph Laplacian absolute-transfer principal eigenvector over selected cochain cells",
                    "hotspots": curvature_hotspots,
                    "nonConclusion": "Perron-Frobenius hotspot ranking is a theorem-candidate analytic reading, not a structural verdict"
                }),
                regime: Some("theorem-candidate".to_string()),
                structural_verdict_ref: None,
            },
        ],
        assumptions: laplacian_assumptions(profile, "checked"),
    })
}

fn evaluate_harmonic_debt_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<HarmonicDebtMeasurementV1, String> {
    let analytic = profile
        .analytic
        .as_ref()
        .and_then(Value::as_object)
        .ok_or_else(|| {
            format!(
                "ag.harmonic-debt requires MeasurementProfile analytic declaration for {}",
                profile.profile_id
            )
        })?;
    let inner_product = analytic
        .get("innerProduct")
        .and_then(Value::as_object)
        .ok_or_else(|| "ag.harmonic-debt analytic.innerProduct is required".to_string())?;
    if inner_product.get("kind").and_then(Value::as_str) != Some("diagonal") {
        return Err("ag.harmonic-debt analytic.innerProduct.kind must be diagonal".to_string());
    }
    let weights = inner_product
        .get("weights")
        .and_then(Value::as_array)
        .ok_or_else(|| "ag.harmonic-debt analytic.innerProduct.weights is required".to_string())?
        .iter()
        .map(|weight| {
            let value = weight
                .as_f64()
                .ok_or_else(|| "harmonic inner-product weights must be numeric".to_string())?;
            if value.is_finite() && value > 0.0 {
                Ok(value)
            } else {
                Err("harmonic inner-product weights must be finite and positive".to_string())
            }
        })
        .collect::<Result<Vec<_>, String>>()?;
    if weights.len() != laplacian_witness_variables(profile).len() {
        return Err(format!(
            "ag.harmonic-debt inner-product weights must match {} witness cells",
            laplacian_witness_variables(profile).len()
        ));
    }
    let laplacian = evaluate_sheaf_laplacian_v1(normalized, profile)?;
    let Some(proxy) = laplacian
        .analytic_readings
        .iter()
        .find(|reading| reading.evaluator == "ag.sheaf-laplacian")
    else {
        return Ok(HarmonicDebtMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("harmonic-debt:{}", profile.profile_id),
                "kind": "harmonic-debt",
                "evaluator": "ag.harmonic-debt",
                "status": "silence_by_design",
                "reason": "cellular_model_missing",
                "whatNext": "supply a validated cellular Laplacian model and witness before evaluating harmonic debt"
            })],
            analytic_readings: Vec::new(),
            assumptions: laplacian.assumptions,
        });
    };
    let harmonic = proxy
        .value
        .get("hodgeDecomposition")
        .and_then(|value| value.get("harmonic"))
        .and_then(Value::as_array)
        .ok_or_else(|| "ag.harmonic-debt requires harmonic decomposition output".to_string())?
        .iter()
        .map(|value| {
            value
                .as_f64()
                .ok_or_else(|| "harmonic values must be numeric".to_string())
        })
        .collect::<Result<Vec<_>, String>>()?;
    if harmonic.len() != weights.len() {
        return Err("harmonic decomposition and inner-product dimensions differ".to_string());
    }
    let harmonic_debt_norm = harmonic
        .iter()
        .zip(weights.iter())
        .map(|(value, weight)| weight * value * value)
        .sum::<f64>()
        .sqrt();
    let cost_model = if let Some(raw_cost_model) = analytic.get("costModel") {
        let model = raw_cost_model
            .as_object()
            .ok_or_else(|| "harmonic costModel must be an object".to_string())?;
        if model.get("kind").and_then(Value::as_str) != Some("lipschitz-harmonic-resolution") {
            return Err(
                "harmonic costModel.kind must be lipschitz-harmonic-resolution".to_string(),
            );
        }
        let lipschitz = model
            .get("lipschitzConstant")
            .and_then(Value::as_f64)
            .ok_or_else(|| "harmonic costModel.lipschitzConstant is required".to_string())?;
        let resolution = model
            .get("harmonicResolution")
            .and_then(Value::as_str)
            .filter(|resolution| !resolution.trim().is_empty())
            .ok_or_else(|| "harmonic costModel.harmonicResolution is required".to_string())?;
        if !lipschitz.is_finite() || lipschitz <= 0.0 {
            return Err(
                "harmonic costModel.lipschitzConstant must be finite and positive".to_string(),
            );
        }
        Some((lipschitz, resolution.to_string()))
    } else {
        None
    };
    let mut assumptions = laplacian.assumptions;
    let (lower_bound, lower_bound_status) = if let Some((lipschitz, resolution)) = cost_model {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/8.7".to_string(),
            assumption: format!("cost model is {lipschitz}-Lipschitz with {resolution}"),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
        (Some(harmonic_debt_norm / lipschitz), "cost_model_supplied")
    } else {
        (None, "cost_model_not_supplied")
    };
    let mut invariant = json!({
        "invariantId": format!("harmonic-debt:{}", profile.profile_id),
        "kind": "harmonic-debt",
        "evaluator": "ag.harmonic-debt",
        "schema": "archsig-measurement-packet/v0.5.4",
        "selectedCoverRef": profile.cover_ref,
        "harmonicDebtNorm": round_f64(harmonic_debt_norm),
        "essentialRepairLowerBound": lower_bound.map(round_f64),
        "lowerBoundStatus": lower_bound_status,
        "sourceProxyReading": proxy.reading_id,
        "nonConclusion": "harmonic debt is an analytic reading and does not establish lawfulness or synthesize a repair"
    });
    let mut reading = json!({
        "readingKind": "harmonic-debt@1",
        "selectedCoverRef": profile.cover_ref,
        "harmonicDebtNorm": round_f64(harmonic_debt_norm),
        "essentialRepairLowerBound": lower_bound.map(round_f64),
        "lowerBoundStatus": lower_bound_status,
        "sourceProxyReadingKind": "graph-laplacian-hodge-proxy@1",
        "certificate": lower_bound.is_some().then(|| "local adjustment cannot reduce repair cost below ||h(g)||/L under the supplied cost model"),
        "nonConclusion": "analytic harmonic debt is not a structural lawfulness verdict"
    });
    if lower_bound.is_none() {
        invariant["status"] = json!("silence_by_design");
        invariant["reason"] = json!("cost_model_not_supplied");
        invariant["whatNext"] = json!(HARMONIC_COST_MODEL_WHAT_NEXT);
        invariant
            .as_object_mut()
            .expect("harmonic debt invariant is object")
            .remove("essentialRepairLowerBound");
        reading
            .as_object_mut()
            .expect("harmonic debt reading is object")
            .remove("essentialRepairLowerBound");
        reading["whatNext"] = json!(HARMONIC_COST_MODEL_WHAT_NEXT);
    }
    Ok(HarmonicDebtMeasurementV1 {
        computed_invariants: vec![invariant],
        analytic_readings: vec![AgAnalyticReadingV1 {
            reading_id: format!("analytic:harmonic-debt:{}", profile.profile_id),
            evaluator: "ag.harmonic-debt".to_string(),
            value: reading,
            regime: Some("analytic-measurement".to_string()),
            structural_verdict_ref: None,
        }],
        assumptions,
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
        "ag.period-stokes d omega audit",
    )?;
    let boundary = stokes_audit_values(
        normalized,
        &selected_contexts,
        "boundaryPeriod",
        "ag.period-stokes boundary audit",
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
                "evaluator": "ag.period-stokes",
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
                "evaluator": "ag.period-stokes",
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
            "evaluator": "ag.period-stokes",
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
            evaluator: "ag.period-stokes".to_string(),
            value: analytic_value,
            regime: Some("analytic-measurement".to_string()),
            structural_verdict_ref: None,
        }],
        assumptions: period_assumptions(profile, "checked"),
    })
}

fn evaluate_period_stokes_audit_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<PeriodAuditMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let cycle_basis = period_audit_witness_cycles(profile);
    let pairings = period_integrals(normalized, &selected_contexts, &cycle_basis)?;
    let d_omega = stokes_audit_values(
        normalized,
        &selected_contexts,
        "dOmegaIntegral",
        "ag.period-stokes-audit d omega audit",
    )?;
    let boundary = stokes_audit_values(
        normalized,
        &selected_contexts,
        "boundaryPeriod",
        "ag.period-stokes-audit boundary audit",
    )?;

    let audit = fixed_coefficient_stokes_audit_report(&d_omega, &boundary, &profile.coefficient);
    let (forms, matrix, analytic_reading) =
        period_pairing_analytic_reading(profile, &cycle_basis, &pairings, Some(audit.clone()));
    let source_refs = pairings
        .iter()
        .flat_map(|pairing| pairing.source_refs.iter())
        .chain(d_omega.iter().flat_map(|entry| entry.source_refs.iter()))
        .chain(boundary.iter().flat_map(|entry| entry.source_refs.iter()))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let computed_invariant = json!({
        "invariantId": format!("period-stokes-audit:{}", profile.profile_id),
        "evaluator": "ag.period-stokes-audit",
        "method": "fixed-coefficient-stokes-audit@1",
        "selectedCoverRef": profile.cover_ref,
        "coefficient": profile.coefficient,
        "forms": forms,
        "cycleBasis": cycle_basis,
        "periodPairingMatrix": rounded_matrix(&matrix),
        "stokesAudit": audit,
        "claimScope": "supplied independent dOmega/boundary accounting values under the selected fixed coefficient reading",
        "analyticReadingRef": analytic_reading.reading_id,
        "sourceRefs": source_refs
    });

    let status = computed_invariant["stokesAudit"]["status"]
        .as_str()
        .unwrap_or("unknown");
    let (verdict, zero, non_zero, method_status, cert_ref, reason, assumption_status) =
        match status {
            "checked" => (
                "measured_zero".to_string(),
                true,
                false,
                "fixed_coefficient_stokes_audit_computed".to_string(),
                Some(format!(
                    "computedInvariants/period-stokes-audit:{}",
                    profile.profile_id
                )),
                "all supplied Stokes audit residuals are zero under the selected fixed coefficient reading".to_string(),
                "checked",
            ),
            "residual_nonzero" => (
                "measured_nonzero".to_string(),
                false,
                true,
                "fixed_coefficient_stokes_audit_computed".to_string(),
                Some(format!(
                    "computedInvariants/period-stokes-audit:{}",
                    profile.profile_id
                )),
                "at least one supplied Stokes audit residual is nonzero under the selected fixed coefficient reading".to_string(),
                "checked",
            ),
            "unknown" => (
                "unknown".to_string(),
                false,
                false,
                "strict_coefficient_unresolved".to_string(),
                None,
                computed_invariant["stokesAudit"]["reason"]
                    .as_str()
                    .unwrap_or("strict coefficient Stokes audit is unresolved")
                    .to_string(),
                "assumed",
            ),
            _ => (
                "unknown".to_string(),
                false,
                false,
                "period_audit_model_missing".to_string(),
                None,
                computed_invariant["stokesAudit"]["reason"]
                    .as_str()
                    .unwrap_or("period Stokes audit model is incomplete")
                    .to_string(),
                "violated",
            ),
        };

    Ok(PeriodAuditMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status,
        cert_ref,
        reason,
        computed_invariants: vec![computed_invariant],
        analytic_readings: vec![analytic_reading],
        assumptions: period_audit_assumptions(profile, assumption_status),
    })
}

fn period_pairing_analytic_reading(
    profile: &MeasurementProfileV1,
    cycle_basis: &[String],
    pairings: &[PeriodIntegralV1],
    stokes_audit: Option<Value>,
) -> (Vec<String>, Vec<Vec<f64>>, AgAnalyticReadingV1) {
    let forms = pairings
        .iter()
        .map(|pairing| pairing.form_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
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
    for pairing in pairings {
        if let (Some(form), Some(cycle)) = (
            form_index.get(&pairing.form_id),
            cycle_index.get(&pairing.cycle_id),
        ) {
            matrix[*form][*cycle] = pairing.value;
        }
    }
    let analytic_value = json!({
        "readingKind": "strict-period-pairing@1",
        "selectedCoverRef": profile.cover_ref,
        "modelRelative": true,
        "forms": forms,
        "cycleBasis": cycle_basis,
        "periodPairingMatrix": rounded_matrix(&matrix),
        "stokesAudit": stokes_audit,
        "nonConclusion": "period pairing is a model-relative analytic reading and is not a structural lawfulness verdict"
    });
    (
        form_index.keys().cloned().collect(),
        matrix,
        AgAnalyticReadingV1 {
            reading_id: format!("analytic:period-stokes:{}", profile.profile_id),
            evaluator: "ag.period-stokes".to_string(),
            value: analytic_value,
            regime: Some("analytic-measurement".to_string()),
            structural_verdict_ref: None,
        },
    )
}

fn evaluate_support_transfer_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<TransferMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let targets = transfer_witness_targets(profile);
    let repair_paths = transfer_repair_paths(normalized, &selected_contexts, &targets)?;
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
                "evaluator": "ag.support-transfer",
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
            "ag.support-transfer transfer pairings reference paths outside selected repair path model: {}",
            outside_paths.join(",")
        ));
    }
    let observed_pairings = pairings
        .iter()
        .map(|pairing| (pairing.path_id.clone(), pairing.target_id.clone()))
        .collect::<BTreeSet<_>>();
    let support_by_path = repair_paths
        .iter()
        .map(|path| {
            (
                path.path_id.clone(),
                path.support_targets
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let support_disjoint_pairings = pairings
        .iter()
        .filter(|pairing| {
            support_by_path
                .get(&pairing.path_id)
                .is_none_or(|support| !support.contains(&pairing.target_id))
        })
        .map(|pairing| format!("{}/{}", pairing.path_id, pairing.target_id))
        .collect::<Vec<_>>();
    if !support_disjoint_pairings.is_empty() {
        return Ok(TransferMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("support-transfer:{}", profile.profile_id),
                "evaluator": "ag.support-transfer",
                "status": "not_computed",
                "reason": format!("support_localized_premise_violated:{}", support_disjoint_pairings.join(",")),
                "supportLocalizedPremise": {
                    "status": "violated",
                    "repairPathSupports": repair_paths.iter().map(|path| json!({
                        "repairPath": path.path_id.clone(),
                        "supportTargets": path.support_targets.clone(),
                        "atomRef": path.atom_ref.clone()
                    })).collect::<Vec<_>>(),
                    "blockedPairings": support_disjoint_pairings,
                    "nonConclusion": "no transfer matrix is filled for pairings outside the supplied repair-path support"
                }
            })],
            analytic_readings: Vec::new(),
            assumptions: transfer_assumptions(profile, "violated"),
        });
    }
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
                "evaluator": "ag.support-transfer",
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
    let support_localized_premise = json!({
        "status": "checked",
        "repairPathCount": repair_paths.len(),
        "targetCount": targets.len(),
        "observedPairingCount": pairings.len(),
        "requiredPairingCount": repair_paths.len() * targets.len(),
        "repairPathSupports": repair_paths.iter().map(|path| json!({
            "repairPath": path.path_id.clone(),
            "supportTargets": path.support_targets.clone(),
            "atomRef": path.atom_ref.clone()
        })).collect::<Vec<_>>(),
        "matrixCompletion": "only supplied repairPath x target support pairings are admitted; any missing pairing blocks computation",
        "nonConclusion": "no unconditional transfer matrix is inferred for support-disjoint or unobserved paths"
    });

    let analytic_value = json!({
        "readingKind": "support-localized-transfer@1",
        "selectedCoverRef": profile.cover_ref,
        "modelRelative": true,
        "supportLocalizedPremise": support_localized_premise.clone(),
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
            "evaluator": "ag.support-transfer",
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
            "supportLocalizedPremise": support_localized_premise,
            "sourceRefs": source_refs
        })],
        analytic_readings: vec![
            AgAnalyticReadingV1 {
                reading_id: format!("analytic:support-transfer:{}", profile.profile_id),
                evaluator: "ag.support-transfer".to_string(),
                value: analytic_value,
                regime: Some("analytic-measurement".to_string()),
                structural_verdict_ref: None,
            },
            AgAnalyticReadingV1 {
                reading_id: format!(
                    "theorem-candidate:transfer-lower-bound:{}",
                    profile.profile_id
                ),
                evaluator: "ag.foundation".to_string(),
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

fn refactor_transport_readings(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    selected_contexts: &BTreeSet<String>,
    structural_verdict: &[AgStructuralVerdictV1],
    refactor_morphism: Option<&Value>,
) -> Vec<AgAnalyticReadingV1> {
    let Some(refactor_morphism) = refactor_morphism else {
        return Vec::new();
    };
    let Ok(validated) = crate::validate_refactor_morphism_v1(refactor_morphism) else {
        return Vec::new();
    };
    let verdict_refs = structural_verdict
        .iter()
        .map(|row| (row.evaluator.clone(), structural_verdict_ref(row)))
        .collect::<BTreeMap<_, _>>();
    normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "refactor")
        .filter(|atom| {
            matches!(
                atom.predicate.as_str(),
                "transportWitness" | "functorialityWitness"
            )
        })
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .filter_map(|atom| {
            let object_tokens = atom
                .object
                .as_deref()
                .map(parse_csv_values)
                .unwrap_or_default()
                .into_iter()
                .collect::<BTreeSet<_>>();
            let (transported_evaluator, transported_ref) = verdict_refs
                .iter()
                .find(|(evaluator, verdict_ref)| {
                    object_tokens.contains(*evaluator) || object_tokens.contains(*verdict_ref)
                })?;
            Some(AgAnalyticReadingV1 {
                reading_id: format!("analytic:refactor-transport:{}", atom.normalized_atom_id),
                evaluator: "ag.foundation".to_string(),
                value: json!({
                    "readingKind": "refactor-verdict-transport@1",
                    "schema": "refactor-morphism/v0.5.4",
                    "morphismId": validated["id"].clone(),
                    "selectedCoverRef": profile.cover_ref.clone(),
                    "witnessAtomRef": atom.normalized_atom_id.clone(),
                    "transportSubject": atom.subject.clone(),
                    "transportObject": atom.object.clone(),
                    "transportedEvaluator": transported_evaluator.clone(),
                    "transportedStructuralVerdictRef": transported_ref.clone(),
                    "predicate": atom.predicate.clone(),
                    "contextRefs": atom.context_memberships.clone(),
                    "sourceRefs": atom.source_refs.clone(),
                    "conclusionCode": ARCHSIG_VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR,
                    "nonConclusion": "refactor transport is emitted only from a validated refactor-morphism artifact and supplied witness data tied to an existing structural verdict; it creates no new verdict or evaluator"
                }),
                regime: Some("analytic-measurement".to_string()),
                structural_verdict_ref: None,
            })
        })
        .collect()
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
        verdict.evaluator == "ag.cech-obstruction" && verdict.verdict == "measured_nonzero"
    });
    let cech_zero = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.cech-obstruction" && verdict.verdict == "measured_zero"
    });
    let cech_cover_shape_excludes = packet.computed_invariants.iter().any(|invariant| {
        invariant["evaluator"] == "ag.cech-obstruction"
            && invariant["theorem12_4Discharge"]["coverShapeExcludesGluingObstruction"].as_bool()
                == Some(true)
    });
    let square_free_nonzero = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.square-free-repair" && verdict.verdict == "measured_nonzero"
    });
    let repair_targets_identified = square_free_nonzero
        && packet.computed_invariants.iter().any(|invariant| {
            invariant["evaluator"] == "ag.square-free-repair"
                && invariant["alexanderDualRepair"]["minimalHittingSets"]
                    .as_array()
                    .is_some_and(|sets| !sets.is_empty())
        });
    let saga_non_gluing = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.saga-descent"
            && verdict.law == "saga.residual-boundary-membership"
            && verdict.verdict == "measured_nonzero"
    });
    let saga_class_nonzero = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.saga-descent"
            && verdict.law == "saga.residual-class"
            && verdict.verdict == "measured_nonzero"
    });
    let saga_glues = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.saga-descent"
            && verdict.law == "saga.global-coherence"
            && verdict.verdict == "measured_zero"
    });
    let conclusion = if saga_class_nonzero {
        ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS
    } else if saga_non_gluing {
        ARCHSIG_SAGA_MEASURED_NONGLUING_RESIDUAL
    } else if saga_glues {
        ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX
    } else if cech_cover_shape_excludes {
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION
    } else if cech_nonzero {
        ARCHSIG_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE
    } else if repair_targets_identified {
        ARCHSIG_REPAIR_TARGETS_IDENTIFIED
    } else if nonzero_count > 0 {
        ARCHSIG_MEASURED_AG_OBSTRUCTION_UNDER_PROFILE
    } else if cech_zero {
        ARCHSIG_NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE
    } else if unmeasured_count > 0 {
        ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE
    } else if packet.structural_verdict.is_empty() {
        ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE
    } else {
        ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE
    };
    let translation_rule = summary_translation_rule(conclusion);
    let mut translation_rule_table = ARCHSIG_ANALYSIS_CONCLUSION_CODES
        .iter()
        .filter(|candidate| {
            **candidate != ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS
                || conclusion == ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS
        })
        .map(|conclusion| summary_translation_rule_json(&summary_translation_rule(conclusion)))
        .collect::<Vec<_>>();
    if packet.analytic_readings.iter().any(|reading| {
        reading.value.get("readingKind").and_then(Value::as_str)
            == Some("refactor-verdict-transport@1")
    }) {
        translation_rule_table.push(summary_translation_rule_json(&summary_translation_rule(
            ARCHSIG_VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR,
        )));
    }
    json!({
        "schema": "archsig-analysis-summary/v0.5.4",
        "conclusion": conclusion,
        "translationRule": active_summary_translation_rule_json(&translation_rule, packet),
        "translationRuleTable": translation_rule_table,
        "readThisFirst": {
            "heading": "Read this first",
            "conclusion": conclusion,
            "whatItMeans": if conclusion == ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION {
                "The selected cover shape and explicit restriction-surjectivity witnesses discharge the Stage 1 abelian cover-shape exclusion check."
            } else if conclusion == ARCHSIG_REPAIR_TARGETS_IDENTIFIED {
                "ArchSig identified combinatorial repair target supports from the selected square-free obstruction invariant."
            } else if cech_nonzero {
                "Local rules are not enough to explain the selected cover; ArchSig measured a cross-context glue mismatch."
            } else if nonzero_count > 0 {
                "Review the theoremRef-bearing structural verdict rows before reading any selected AG obstruction claim."
            } else if cech_zero {
                "No selected H1 glue mismatch was measured under the profile."
            } else if unmeasured_count > 0 {
                "ArchSig produced a profile-relative foundation result with unmeasured, unknown, or not_computed rows still visible."
            } else {
                "ArchSig produced a profile-relative foundation result for the selected measurement surface."
            },
            "whereToLookFirst": "See archsig-insight-report.json#/insightCards/0/evidence",
            "nextAction": "Open archsig-insight-brief.md or the viewer Insight Queue.",
            "boundary": if conclusion == ARCHSIG_REPAIR_TARGETS_IDENTIFIED {
                "Profile-relative. Principle 5.3 boundary: repair targets are combinatorial hitting-set supports, not automatic semantic repairs or operation semantics.".to_string()
            } else if conclusion == ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION {
                format!(
                    "Profile-relative abelian cover-shape statement. Non-abelian torsor, stacky descent, and gerbe obstructions are not excluded. {} assumptions declared. {} non-terminal rows.",
                    packet.assumptions.iter().filter(|row| row.status == "assumed").count(),
                    unmeasured_count
                )
            } else {
                format!(
                    "Profile-relative. {} assumptions declared. {} non-terminal rows.",
                    packet.assumptions.iter().filter(|row| row.status == "assumed").count(),
                    unmeasured_count
                )
            }
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
        "schema": "archsig-insight-report/v0.5.4",
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
            "Insight report is a projection of archsig-measurement-packet/v0.5.4 and does not generate new measurement claims.",
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
        if row.evaluator == "ag.cech-obstruction" && row.verdict == "measured_nonzero" {
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
        } else if row.evaluator == "ag.cech-obstruction" && row.verdict == "measured_zero" {
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
        } else if row.evaluator == "ag.square-free-repair" && row.verdict == "measured_nonzero" {
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
        } else if row.evaluator == "ag.law-conflict-tor" && row.verdict == "measured_nonzero" {
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
                if row.evaluator == "ag.law-conflict-tor" {
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
        .any(|reading| reading.evaluator == "ag.sheaf-laplacian")
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
    let analytic_overlay_refs = analytic_overlay_scene_refs(packet, gluing_geometry);
    let period_stokes_refs = period_stokes_scene_refs(packet, gluing_geometry);
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
    let has_analytic_overlay =
        !string_array_at(&analytic_overlay_refs, &["overlayRefs"]).is_empty();
    let has_period_stokes = gluing_geometry["periodStokes"]["activeMeterCount"]
        .as_u64()
        .unwrap_or_default()
        > 0;
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
        with_scene_non_claims(
            scene_v1(
                "analytic-overlay",
                "analytic_overlay",
                "Analytic Overlay",
                "Which measured analytic readings can be inspected without promoting them to verdicts?",
                (
                    "analytic source family",
                    "selected cover or support stratum",
                    "reading magnitude / proxy height",
                ),
                "analytic_overlay_lane",
                "overlay",
                "analyticOverlay",
                "packet analytic reading overlay; no new structural verdict",
                &analytic_overlay_refs,
                "analytic_reading",
                "heat",
                "contour",
                has_analytic_overlay,
            ),
            &[
                "Analytic overlays are packet projections only; they do not create structural verdicts.",
                "Near-flat or low proxy values are not measured_zero lawfulness.",
            ],
        ),
        with_scene_non_claims(
            scene_v1(
                "period-stokes",
                "period_stokes_meter",
                "Period Stokes Meter",
                "Does the supplied finite period audit close under the selected coefficient reading?",
                (
                    "period cycle basis",
                    "form / chain audit pair",
                    "Stokes residual magnitude",
                ),
                "period_stokes_meter",
                "meter",
                "periodStokesMeter",
                "M9 Stokes audit meter; modelRelative finite-period reading",
                &period_stokes_refs,
                if has_period_stokes {
                    "analytic_reading"
                } else {
                    "not_applicable"
                },
                "ring",
                "flow_arc",
                has_period_stokes,
            ),
            &[
                "Period Stokes meter is modelRelative to the supplied finite period model.",
                "Period arcs and audit residuals are packet projections; the viewer creates no new structural verdict.",
            ],
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
            "spectrumLandscapeRef": "gluingGeometry.spectrumLandscape",
            "projectionObjectKinds": [
                "curvatureHeightField",
                "blockedUnmeasuredRegion",
                "spectrumLawfulPlain",
                "spectrumLocalDeviationPeak",
                "spectrumProxyRidge"
            ]
        }),
        "analytic-overlay" => json!({
            "analyticOverlayBundleRef": "gluingGeometry.analyticOverlayBundle",
            "projectionObjectKinds": [
                "periodPairingMatrixOverlay",
                "transferCostOverlay",
                "spectralGapOverlay",
                "curvatureHotspotOverlay",
                "singularityConcentrationOverlay"
            ]
        }),
        "period-stokes" => json!({
            "periodStokesRef": "gluingGeometry.periodStokes",
            "projectionObjectKinds": [
                "periodStokesCycleArc",
                "periodStokesAuditMeter",
                "periodStokesResidualFlux"
            ]
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
        "Scene geometry is a bounded projection of archsig-measurement-packet/v0.5.4 and archsig-insight-report/v0.5.4; it does not create a new structural verdict."
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

fn analytic_overlay_scene_refs(
    packet: &ArchSigMeasurementPacketV1,
    gluing_geometry: &Value,
) -> Value {
    let overlays = gluing_geometry["analyticOverlayBundle"]["overlays"]
        .as_array()
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let overlay_refs = overlays
        .iter()
        .filter_map(|overlay| overlay["overlayId"].as_str())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let analytic_reading_refs = overlays
        .iter()
        .filter_map(|overlay| overlay["sourceReadingRef"].as_str())
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let invariant_refs = overlays
        .iter()
        .filter_map(|overlay| overlay["sourceInvariantRef"].as_str())
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    json!({
        "overlayRefs": overlay_refs,
        "analyticReadingRefs": analytic_reading_refs,
        "invariantRefs": invariant_refs,
        "coverRefs": [packet.profile.cover_ref.clone()],
        "sourceRefs": []
    })
}

fn period_stokes_scene_refs(packet: &ArchSigMeasurementPacketV1, gluing_geometry: &Value) -> Value {
    let meters = gluing_geometry["periodStokes"]["meters"]
        .as_array()
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let meter_refs = meters
        .iter()
        .filter_map(|meter| meter["meterId"].as_str())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let invariant_refs = meters
        .iter()
        .filter_map(|meter| meter["sourceInvariantRef"].as_str())
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let structural_verdict_refs = meters
        .iter()
        .filter_map(|meter| meter["structuralVerdictRef"].as_str())
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    json!({
        "meterRefs": meter_refs,
        "invariantRefs": invariant_refs,
        "structuralVerdictRefs": structural_verdict_refs,
        "coverRefs": [packet.profile.cover_ref.clone()],
        "sourceRefs": []
    })
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
                "analytic_reading": "blue analytic reading lane; never promoted to structural zero",
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
    let cover_nerve_projection =
        project_h2_coherence_to_cover_nerve(cover_nerve_projection, packet);
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
    let analytic_overlay_bundle = analytic_overlay_bundle_projection(packet);
    let period_stokes = period_stokes_projection(packet);
    let spectrum_landscape = spectrum_landscape_projection(packet);
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
    let analytic_overlay_count = analytic_overlay_bundle["rawOverlayCount"]
        .as_u64()
        .unwrap_or_default() as usize;
    let period_stokes_meter_count =
        period_stokes["rawMeterCount"].as_u64().unwrap_or_default() as usize;
    let spectrum_cell_count = spectrum_landscape["rawCellCount"]
        .as_u64()
        .unwrap_or_default() as usize;
    let cocycle_support_edge_count = nonzero_edges.len();
    let cocycle_support_edges = nonzero_edges
        .iter()
        .take(GLUING_COCYCLE_EDGE_RENDER_LIMIT)
        .map(|edge| {
            json!({
                "edgeId": edge.edge_id,
                "sourceContextRef": edge.source_context,
                "targetContextRef": edge.target_context,
                "value": edge.value,
                "supportAtomRefs": edge.support_atom_refs
            })
        })
        .collect::<Vec<_>>();
    json!({
        "schema": "archsig-viewer-gluing-geometry/v0.5.4",
        "sourcePacketRef": "archsig-measurement-packet.json",
        "sourceInsightReportRef": "archsig-insight-report.json",
        "projectionBoundary": "This geometry translates measured packet and ArchMap cover support into viewer objects. It adds no structural verdict or monodromy verdict; H2 coherence color appears only when projected from ag.coherence-obstruction packet verdicts.",
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
            "supportEdges": cocycle_support_edges,
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
        "analyticOverlayBundle": analytic_overlay_bundle,
        "periodStokes": period_stokes,
        "spectrumLandscape": spectrum_landscape,
        "visualEncodingLegend": visual_encoding_legend_v1(),
        "renderLimits": {
            "nerveTriangles": GLUING_TRIANGLE_RENDER_LIMIT,
            "cocycleSupportEdges": GLUING_COCYCLE_EDGE_RENDER_LIMIT,
            "curvatureFieldRows": GLUING_FIELD_ROW_RENDER_LIMIT,
            "curvatureRegions": GLUING_REGION_RENDER_LIMIT,
            "forbiddenCages": GLUING_CAGE_RENDER_LIMIT,
            "repairMorphs": GLUING_MORPH_RENDER_LIMIT,
            "atomGlyphs": GLUING_ATOM_GLYPH_RENDER_LIMIT,
            "analyticOverlays": ANALYTIC_OVERLAY_RENDER_LIMIT,
            "periodStokesMeters": PERIOD_STOKES_METER_RENDER_LIMIT,
            "spectrumCells": GLUING_FIELD_ROW_RENDER_LIMIT
        },
        "omittedGeometryCounts": {
            "nerveTriangles": triangle_count.saturating_sub(GLUING_TRIANGLE_RENDER_LIMIT),
            "cocycleSupportEdges": cocycle_support_edge_count.saturating_sub(GLUING_COCYCLE_EDGE_RENDER_LIMIT),
            "curvatureFieldRows": field_row_count.saturating_sub(GLUING_FIELD_ROW_RENDER_LIMIT),
            "measuredZeroRegions": zero_region_count.saturating_sub(GLUING_REGION_RENDER_LIMIT),
            "blockedRegions": blocked_region_count.saturating_sub(GLUING_REGION_RENDER_LIMIT),
            "forbiddenCages": forbidden_cages.len().saturating_sub(GLUING_CAGE_RENDER_LIMIT),
            "repairMorphs": repair_morphs.len().saturating_sub(GLUING_MORPH_RENDER_LIMIT),
            "atomGlyphs": atom_glyph_total_count.saturating_sub(GLUING_ATOM_GLYPH_RENDER_LIMIT),
            "analyticOverlays": analytic_overlay_count.saturating_sub(ANALYTIC_OVERLAY_RENDER_LIMIT),
            "periodStokesMeters": period_stokes_meter_count.saturating_sub(PERIOD_STOKES_METER_RENDER_LIMIT),
            "spectrumCells": spectrum_cell_count.saturating_sub(GLUING_FIELD_ROW_RENDER_LIMIT)
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
    _normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
) -> Vec<Value> {
    let mut cages = Vec::new();
    for invariant in &packet.computed_invariants {
        let generators = invariant["obstructionIdeal"]["generators"]
            .as_array()
            .into_iter()
            .flatten();
        for generator in generators {
            let support_atom_refs = string_array_at(generator, &["supportAtomRefs"]);
            let support_variables = string_array_at(generator, &["support"]);
            // Declared support variables do not create measured geometry. A
            // cage is projected only when the packet carries observed atom
            // references for that generator.
            if support_atom_refs.is_empty() {
                continue;
            }
            let generator_id = string_field(generator, "generatorId");
            cages.push(json!({
                "cageId": format!("forbidden-cage:{generator_id}"),
                "atomRefs": support_atom_refs,
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
    if forbidden_cages.is_empty() {
        return Vec::new();
    }
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
        .filter_map(|(index, candidate)| {
            let candidate_variables = string_array_at(candidate, &["supportVariables"]);
            let related_cages = related_forbidden_cages(forbidden_cages, candidate);
            if related_cages.is_empty() {
                return None;
            }
            let from_cage_ref = related_cages
                .get(index % related_cages.len().max(1))
                .or_else(|| related_cages.first())
                .cloned()?;
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
            Some(json!({
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
            }))
        })
        .collect()
}

fn analytic_overlay_bundle_projection(packet: &ArchSigMeasurementPacketV1) -> Value {
    let mut period_pairing = Vec::new();
    let mut transfer_cost = Vec::new();
    let mut spectral_gap = Vec::new();
    let mut curvature_hotspot = Vec::new();

    for reading in &packet.analytic_readings {
        let reading_kind = string_at(&reading.value, &["readingKind"]);
        match reading_kind.as_str() {
            "strict-period-pairing@1" => {
                period_pairing.push(json!({
                    "overlayId": format!("overlay:period-pairing:{}", stable_ref_segment(&reading.reading_id)),
                    "overlayKind": "period_pairing_matrix",
                    "sourceReadingRef": reading.reading_id,
                    "sourceEvaluator": reading.evaluator,
                    "sourceReadingKind": reading_kind,
                    "sourceRegime": reading.regime,
                    "colorRole": "analytic_reading",
                    "forms": reading.value["forms"].clone(),
                    "cycleBasis": reading.value["cycleBasis"].clone(),
                    "periodPairingMatrix": reading.value["periodPairingMatrix"].clone(),
                    "nonClaim": reading.value["nonConclusion"].clone(),
                    "projectionBoundary": "modelRelative period landscape; not a structural verdict"
                }));
            }
            "support-localized-transfer@1" => {
                transfer_cost.push(json!({
                    "overlayId": format!("overlay:transfer-cost:{}", stable_ref_segment(&reading.reading_id)),
                    "overlayKind": "wasserstein_transfer_cost",
                    "sourceReadingRef": reading.reading_id,
                    "sourceEvaluator": reading.evaluator,
                    "sourceReadingKind": reading_kind,
                    "sourceRegime": reading.regime,
                    "colorRole": "analytic_reading",
                    "repairPaths": reading.value["repairPaths"].clone(),
                    "transferTargets": reading.value["transferTargets"].clone(),
                    "transferMeasurementPairing": reading.value["transferMeasurementPairing"].clone(),
                    "transferResidue": reading.value["transferResidue"].clone(),
                    "wassersteinTransferCost": reading.value["wassersteinTransferCost"].clone(),
                    "nonClaim": "Wasserstein transfer cost is a supplied finite support-localized analytic reading; it is not W1 itself and does not prove global repair safety.",
                    "projectionBoundary": reading.value["nonConclusion"].clone()
                }));
            }
            "graph-laplacian-hodge-proxy@1" => {
                spectral_gap.push(json!({
                    "overlayId": format!("overlay:spectral-gap:{}", stable_ref_segment(&reading.reading_id)),
                    "overlayKind": "spectral_gap_proxy",
                    "sourceReadingRef": reading.reading_id,
                    "sourceEvaluator": reading.evaluator,
                    "sourceReadingKind": reading_kind,
                    "sourceRegime": reading.regime,
                    "colorRole": "analytic_reading",
                    "cells": reading.value["cells"].clone(),
                    "spectralGap": reading.value["spectralGap"].clone(),
                    "harmonicMass": reading.value["harmonicMass"].clone(),
                    "distanceToFlatness": reading.value["distanceToFlatness"].clone(),
                    "nonClaim": "spectralGap is a finite graph-Laplacian proxy eigenvalue, not L1 and not measured_zero lawfulness.",
                    "projectionBoundary": reading.value["nonConclusion"].clone()
                }));
            }
            "curvature-transfer-perron-hotspot@1" => {
                curvature_hotspot.push(json!({
                    "overlayId": format!("overlay:curvature-hotspot:{}", stable_ref_segment(&reading.reading_id)),
                    "overlayKind": "curvature_spectrum_hotspot",
                    "sourceReadingRef": reading.reading_id,
                    "sourceEvaluator": reading.evaluator,
                    "sourceReadingKind": reading_kind,
                    "sourceRegime": reading.regime,
                    "colorRole": "analytic_reading",
                    "hotspots": reading.value["hotspots"].clone(),
                    "nonClaim": reading.value["nonConclusion"].clone(),
                    "projectionBoundary": "hotspot projection is gated by the landed theorem-candidate reading; it creates no structural verdict"
                }));
            }
            _ => {}
        }
    }

    let singularity_concentration = packet
        .computed_invariants
        .iter()
        .filter(|invariant| invariant["evaluator"] == "ag.law-conflict-tor")
        .flat_map(|invariant| {
            invariant["lawConflicts"]
                .as_array()
                .into_iter()
                .flatten()
                .enumerate()
                .map(|(index, conflict)| {
                    let shared_support = string_array_at(conflict, &["sharedSupport"]);
                    json!({
                        "overlayId": format!(
                            "overlay:singularity-concentration:{}:{index}",
                            stable_ref_segment(&string_field(invariant, "invariantId"))
                        ),
                        "overlayKind": "singularity_concentration",
                        "sourceInvariantRef": invariant["invariantId"],
                        "sourceEvaluator": invariant["evaluator"],
                        "colorRole": "analytic_reading",
                        "stratumRef": if shared_support.is_empty() {
                            format!("law-conflict-stratum:{index}")
                        } else {
                            format!("law-conflict-stratum:{}", shared_support.join("+"))
                        },
                        "sharedSupport": shared_support,
                        "multidegree": conflict["multidegree"].clone(),
                        "commonAmbient": invariant["commonAmbient"].clone(),
                        "concentrationCount": 1,
                        "deformationRegime": "not_provided",
                        "nonClaim": "singularity concentration is a selected LawConflict_1 count projection only; deformation regime is not provided and this is not object size or repair difficulty."
                    })
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let raw_overlay_count = period_pairing.len()
        + transfer_cost.len()
        + spectral_gap.len()
        + curvature_hotspot.len()
        + singularity_concentration.len();

    period_pairing.truncate(ANALYTIC_OVERLAY_RENDER_LIMIT);
    transfer_cost.truncate(ANALYTIC_OVERLAY_RENDER_LIMIT);
    spectral_gap.truncate(ANALYTIC_OVERLAY_RENDER_LIMIT);
    curvature_hotspot.truncate(ANALYTIC_OVERLAY_RENDER_LIMIT);
    let mut singularity_concentration = singularity_concentration;
    singularity_concentration.truncate(ANALYTIC_OVERLAY_RENDER_LIMIT);

    let overlays = period_pairing
        .iter()
        .chain(transfer_cost.iter())
        .chain(spectral_gap.iter())
        .chain(curvature_hotspot.iter())
        .chain(singularity_concentration.iter())
        .take(ANALYTIC_OVERLAY_RENDER_LIMIT)
        .cloned()
        .collect::<Vec<_>>();

    json!({
        "schema": "archsig-analytic-overlay-bundle/v0.5.4",
        "allowlist": [
            "strict-period-pairing@1",
            "support-localized-transfer@1",
            "graph-laplacian-hodge-proxy@1",
            "curvature-transfer-perron-hotspot@1",
            "ag.law-conflict-tor/lawConflicts"
        ],
        "colorRole": "analytic_reading",
        "rawOverlayCount": raw_overlay_count,
        "projectionBoundary": "This bundle projects existing packet analytic readings and computed invariants into the viewer; it creates no structural verdict and never promotes analytic values to measured_zero.",
        "periodPairingOverlays": period_pairing,
        "transferCostOverlays": transfer_cost,
        "spectralGapOverlays": spectral_gap,
        "curvatureHotspotOverlays": curvature_hotspot,
        "singularityConcentrationOverlays": singularity_concentration,
        "overlays": overlays,
        "nonClaims": [
            "Period overlays are model-relative.",
            "Transfer cost overlays are finite support-localized readings, not global repair safety.",
            "Spectral gap overlays are proxy eigenvalues and are not structural lawfulness.",
            "Curvature hotspot overlays are theorem-candidate projections.",
            "Singularity concentration has deformationRegime=not_provided and is not a size or difficulty score."
        ]
    })
}

fn period_stokes_projection(packet: &ArchSigMeasurementPacketV1) -> Value {
    let structural_verdict = packet
        .structural_verdict
        .iter()
        .find(|row| row.evaluator == "ag.period-stokes-audit");
    let structural_verdict_ref = structural_verdict.map(structural_verdict_ref);
    let structural_verdict_value = structural_verdict
        .map(|row| row.verdict.clone())
        .unwrap_or_else(|| "not_computed".to_string());
    let meters = packet
        .computed_invariants
        .iter()
        .filter(|invariant| invariant["evaluator"] == "ag.period-stokes-audit")
        .take(PERIOD_STOKES_METER_RENDER_LIMIT)
        .enumerate()
        .map(|(index, invariant)| {
            let cycle_basis = string_array_at(invariant, &["cycleBasis"]);
            let forms = string_array_at(invariant, &["forms"]);
            let pairs = invariant["stokesAudit"]["pairs"]
                .as_array()
                .cloned()
                .unwrap_or_default();
            let audit_status = invariant["stokesAudit"]["status"]
                .as_str()
                .unwrap_or("unknown");
            let has_model = !cycle_basis.is_empty() && !pairs.is_empty();
            let meter_status = if audit_status == "checked" || audit_status == "residual_nonzero" {
                "structural_audit_projected"
            } else if audit_status == "unknown" && !cycle_basis.is_empty() {
                "analytic_only"
            } else if !has_model {
                "silent"
            } else {
                "analytic_only"
            };
            json!({
                "meterId": format!(
                    "period-stokes-meter:{}:{index}",
                    stable_ref_segment(&string_field(invariant, "invariantId"))
                ),
                "sourceInvariantRef": invariant["invariantId"],
                "sourceEvaluator": "ag.period-stokes-audit",
                "structuralVerdictRef": structural_verdict_ref.clone(),
                "structuralVerdict": structural_verdict_value.clone(),
                "meterStatus": meter_status,
                "auditStatus": audit_status,
                "colorRole": "analytic_reading",
                "modelRelative": true,
                "selectedCoverRef": invariant["selectedCoverRef"],
                "coefficient": invariant["coefficient"],
                "forms": forms,
                "cycleBasis": cycle_basis,
                "periodPairingMatrix": invariant["periodPairingMatrix"],
                "stokesAudit": invariant["stokesAudit"],
                "pairCount": pairs.len(),
                "maxAbsoluteResidual": invariant["stokesAudit"]["maxAbsoluteResidual"],
                "nonzeroPairCount": invariant["stokesAudit"]["nonzeroPairCount"],
                "nonClaim": "Stokes audit meter is modelRelative to the supplied finite period model; it visualizes packet audit residuals and creates no new structural verdict.",
                "projectionBoundary": "periodStokes projection carries M9 packet values only; analytic period arcs are not absolute periods and not lawfulness verdicts"
            })
        })
        .collect::<Vec<_>>();
    let active_meter_count = meters
        .iter()
        .filter(|meter| meter["meterStatus"] == "structural_audit_projected")
        .count();
    let raw_meter_count = packet
        .computed_invariants
        .iter()
        .filter(|invariant| invariant["evaluator"] == "ag.period-stokes-audit")
        .count();
    json!({
        "schema": "archsig-period-stokes-meter/v0.5.4",
        "sourceEvaluator": "ag.period-stokes-audit",
        "sourceAnalyticReadingKind": "strict-period-pairing@1",
        "colorRole": "analytic_reading",
        "modelRelative": true,
        "rawMeterCount": raw_meter_count,
        "activeMeterCount": active_meter_count,
        "meterCount": meters.len(),
        "meters": meters,
        "projectionBoundary": "This projection renders M9 Stokes audit values in the viewer; it does not create or modify structural verdict rows.",
        "nonClaims": [
            "Period arcs are modelRelative to the supplied finite period model.",
            "The meter reads packet stokesAudit pairs; it is not an absolute period invariant.",
            "Unknown or model-missing audits remain analytic-only or silent, never green structural closure."
        ]
    })
}

fn spectrum_landscape_projection(packet: &ArchSigMeasurementPacketV1) -> Value {
    let hodge_reading = packet.analytic_readings.iter().find(|reading| {
        string_at(&reading.value, &["readingKind"]) == "graph-laplacian-hodge-proxy@1"
    });
    let hotspot_reading = packet.analytic_readings.iter().find(|reading| {
        string_at(&reading.value, &["readingKind"]) == "curvature-transfer-perron-hotspot@1"
    });
    let Some(reading) = hodge_reading else {
        return json!({
            "schema": "archsig-spectrum-landscape/v0.5.4",
            "status": "silent",
            "measurementStatus": "not_projected",
            "colorRole": "analytic_reading",
            "rawCellCount": 0,
            "cells": [],
            "hotspots": [],
            "projectionBoundary": "No M10 graph-laplacian-hodge-proxy reading is present; viewer remains silent and creates no structural verdict."
        });
    };
    let cells = string_array_at(&reading.value, &["cells"]);
    let cochain = reading.value["cochain"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let transfer_rows = reading.value["curvatureTransferSpectrum"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let transfer_by_cell = transfer_rows
        .iter()
        .filter_map(|row| {
            Some((
                string_field(row, "cell"),
                row["curvature"].as_f64().unwrap_or(0.0),
            ))
        })
        .collect::<BTreeMap<_, _>>();
    let cell_rows = cells
        .iter()
        .take(GLUING_FIELD_ROW_RENDER_LIMIT)
        .enumerate()
        .map(|(index, cell)| {
            let cochain_value = cochain.get(index).and_then(Value::as_f64).unwrap_or(0.0);
            let curvature = transfer_by_cell.get(cell).copied().unwrap_or(0.0);
            json!({
                "cellRef": cell,
                "axisRef": format!("spectrum-axis:{cell}"),
                "cochainValue": round_f64(cochain_value),
                "signedCurvature": round_f64(curvature),
                "plainRole": if cochain_value.abs() < 1.0e-9 {
                    "lawful_plain_measured_zero"
                } else {
                    "local_deviation"
                },
                "deterministicIndex": index,
                "colorRole": "analytic_reading",
                "measurementStatus": "proxy",
                "notLegacyStatusField": true
            })
        })
        .collect::<Vec<_>>();
    let hotspot_rows = hotspot_reading
        .map(|reading| {
            reading.value["hotspots"]
                .as_array()
                .into_iter()
                .flatten()
                .take(GLUING_FIELD_ROW_RENDER_LIMIT)
                .enumerate()
                .map(|(index, hotspot)| {
                    json!({
                        "hotspotId": format!(
                            "spectrum-hotspot:{}:{index}",
                            stable_ref_segment(&reading.reading_id)
                        ),
                        "cellRef": string_field(hotspot, "cell"),
                        "axisRef": format!("spectrum-axis:{}", string_field(hotspot, "cell")),
                        "hotspotWeight": hotspot["hotspotWeight"].clone(),
                        "status": "needsReview",
                        "measurementStatus": "proxy",
                        "colorRole": "analytic_reading",
                        "sourceReadingRef": reading.reading_id,
                        "sourceRegime": reading.regime,
                        "localDeviationSecondary": true
                    })
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let spectral_radius_value = reading
        .value
        .get("spectralRadius")
        .or_else(|| reading.value.get("spectralGap"))
        .cloned()
        .unwrap_or(Value::Null);
    let spectral_radius_numeric = spectrum_numeric_value(&spectral_radius_value);

    json!({
        "schema": "archsig-spectrum-landscape/v0.5.4",
        "status": "needsReview",
        "measurementStatus": "proxy",
        "sourceReadingRef": reading.reading_id,
        "sourceEvaluator": reading.evaluator,
        "sourceReadingKind": "graph-laplacian-hodge-proxy@1",
        "hotspotReadingRef": hotspot_reading.map(|reading| reading.reading_id.clone()),
        "hotspotReadingKind": hotspot_reading.map(|_| "curvature-transfer-perron-hotspot@1"),
        "selectedCoverRef": reading.value["selectedCoverRef"].clone(),
        "colorRole": "analytic_reading",
        "rawCellCount": cells.len(),
        "cells": cell_rows,
        "hotspots": hotspot_rows,
        "spectralGap": reading.value["spectralGap"].clone(),
        "spectralRadius": spectral_radius_value,
        "spectralRadiusNumeric": spectral_radius_numeric.map(round_f64),
        "axisPlacement": "axisRef-deterministic",
        "forbiddenFieldRefs": ["legacy-schema052-curvature-status"],
        "nonClaim": "Spectrum landscape is an analytic proxy reading; lawful plain and hotspots are not structural verdicts.",
        "projectionBoundary": "spectrumLandscape carries M10/M14 packet readings only; no legacy v0 status field is read and no structural verdict is created."
    })
}

fn spectrum_numeric_value(value: &Value) -> Option<f64> {
    value
        .as_f64()
        .or_else(|| value.as_str().and_then(|text| text.parse::<f64>().ok()))
        .filter(|value| value.is_finite())
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
                "colorRole": "analytic_reading",
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
    if is_local_or_private_source_ref(source_ref) {
        "source-ref:redacted-local-path".to_string()
    } else {
        source_ref.to_string()
    }
}

fn is_local_or_private_source_ref(source_ref: &str) -> bool {
    source_ref.starts_with('/')
        || source_ref.starts_with("~/")
        || source_ref.starts_with("../")
        || source_ref.contains("/../")
        || source_ref.contains('\\')
        || looks_like_windows_drive_path(source_ref)
        || has_hidden_path_segment(source_ref)
}

fn looks_like_windows_drive_path(source_ref: &str) -> bool {
    let bytes = source_ref.as_bytes();
    bytes.len() >= 3
        && bytes[0].is_ascii_alphabetic()
        && bytes[1] == b':'
        && matches!(bytes[2], b'/' | b'\\')
}

fn has_hidden_path_segment(source_ref: &str) -> bool {
    source_ref
        .split(['/', '\\'])
        .any(|segment| segment.starts_with('.') && segment != "." && segment != "..")
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
        "no_measured_glue_mismatch" => 300,
        "measurement_boundary" => 200,
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
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    reason: String,
    cert_ref: Option<String>,
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
    // true only when the edge value comes from recorded observations: an
    // explicit cocycleValue atom, or sectionValue atoms on both endpoints.
    observed: bool,
}

fn evaluate_cech_obstruction_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    execution_plan: Option<&LawExecutionPlanV1>,
) -> CechMeasurementV1 {
    let selected_contexts = selected_cover_contexts(normalized, profile);
    let derived_edges = cech_edges(normalized, &selected_contexts);
    let edges = execution_plan
        .and_then(|plan| plan.cech_edges.as_ref())
        .map(|selected_edges| {
            derived_edges
                .iter()
                .filter(|edge| {
                    let mut pair = [edge.source_context.clone(), edge.target_context.clone()];
                    pair.sort();
                    selected_edges.contains(&pair)
                })
                .cloned()
                .collect::<Vec<_>>()
        })
        .unwrap_or(derived_edges);
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
    let empty_selected_scope = selected_contexts.is_empty() || edges.is_empty();
    let nerve_is_forest = !empty_selected_scope
        && edges.len().saturating_add(component_count) == selected_contexts.len();
    let has_triple_overlap_faces = cover_nerve_face_count > 0;
    let restriction_surjectivity_witnesses =
        restriction_surjectivity_witnesses_v1(normalized, &edges);
    let selected_restriction_edges = edges
        .iter()
        .map(|edge| edge.edge_id.as_str())
        .collect::<BTreeSet<_>>();
    let witnessed_restriction_edges = restriction_surjectivity_witnesses
        .iter()
        .filter_map(|witness| witness["edgeRef"].as_str())
        .collect::<BTreeSet<_>>();
    let restriction_surjectivity_checked = !empty_selected_scope
        && !edges.is_empty()
        && witnessed_restriction_edges == selected_restriction_edges;
    let cover_shape_excludes_gluing_obstruction =
        nerve_is_forest && !has_triple_overlap_faces && restriction_surjectivity_checked;
    let observed_edges = edges
        .iter()
        .filter(|edge| edge.observed)
        .cloned()
        .collect::<Vec<_>>();
    let unobserved_edge_refs = edges
        .iter()
        .filter(|edge| !edge.observed)
        .map(|edge| edge.edge_id.clone())
        .collect::<Vec<_>>();
    // The measured cochain is restricted to observed edges: an unobserved edge
    // carries no section evidence, so it must not enter the cocycle as a zero.
    // Shape-level facts (nerve, H1 capacity, forest exclusion) stay on the full
    // selected 1-skeleton because they do not depend on section observations.
    let sections_not_observed = !empty_selected_scope
        && observed_edges.is_empty()
        && !cover_shape_excludes_gluing_obstruction;
    let h1_class_nonzero = !empty_selected_scope
        && !sections_not_observed
        && !edge_cochain_is_coboundary(&selected_contexts, &observed_edges);
    let topological_debt_capacity = topological_debt_capacity_invariant_v1(
        profile,
        &selected_contexts,
        &edges,
        &cover_nerve_projection,
        h1_dimension,
        h1_class_nonzero,
        empty_selected_scope,
    );
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
    let mut assumptions = vec![
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
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/12.3".to_string(),
            assumption: "constant coefficient nerve b1 comparison".to_string(),
            status: "checked".to_string(),
            checked_by: Some(format!(
                "measurement-profile:{}.coefficient={}",
                profile.profile_id, profile.coefficient
            )),
            assumed_by: None,
        },
    ];
    assumptions.extend(cech_effectivity_assumptions_v1(
        profile,
        nerve_is_forest,
        has_triple_overlap_faces,
        restriction_surjectivity_checked,
    ));
    if empty_selected_scope {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/B.8.2-empty-selected-scope".to_string(),
            assumption: "U-adequate cover selects a non-empty Cech 1-skeleton".to_string(),
            status: "violated".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
    }
    if sections_not_observed {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/B.8.2-sections-not-observed".to_string(),
            assumption: "section observations cover at least one selected Cech edge".to_string(),
            status: "violated".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
    }

    let (verdict, zero, non_zero, method_status, reason) = if empty_selected_scope {
        (
            "not_computed".to_string(),
            false,
            false,
            "empty_selected_scope".to_string(),
            "empty_selected_scope: selected cover has no non-empty Cech 1-skeleton for ag.cech-obstruction".to_string(),
        )
    } else if sections_not_observed {
        (
            "not_computed".to_string(),
            false,
            false,
            "sections_not_observed".to_string(),
            "sections_not_observed: no sectionValue or cocycleValue observation covers any selected Cech edge; supply section observations on both endpoint contexts of a selected edge (or an explicit cocycleValue for the edge) before the H1 class can be measured".to_string(),
        )
    } else if h1_class_nonzero {
        (
            "measured_nonzero".to_string(),
            false,
            true,
            "finite_f2_cech_computed".to_string(),
            "finite F2 Cech 1-cocycle is not a coboundary on the selected cover".to_string(),
        )
    } else {
        (
            "measured_zero".to_string(),
            true,
            false,
            "finite_f2_cech_computed".to_string(),
            "finite F2 Cech 1-cocycle is zero or a coboundary on the selected cover".to_string(),
        )
    };
    let cert_ref = if empty_selected_scope || sections_not_observed {
        None
    } else {
        Some(format!(
            "computedInvariants/cech-cohomology:{}",
            profile.profile_id
        ))
    };

    CechMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status,
        reason,
        cert_ref,
        computed_invariants: vec![
            json!({
                "invariantId": format!("cech-cohomology:{}", profile.profile_id),
                "evaluator": "ag.cech-obstruction",
                "method": "finite-f2-incidence-graph-cochain@1",
                "status": if empty_selected_scope || sections_not_observed {
                    "not_computed"
                } else {
                    "computed"
                },
                "methodStatus": if empty_selected_scope {
                    "empty_selected_scope"
                } else if sections_not_observed {
                    "sections_not_observed"
                } else {
                    "finite_f2_cech_computed"
                },
                "reason": if empty_selected_scope {
                    "empty_selected_scope: selected cover has no non-empty Cech 1-skeleton for ag.cech-obstruction"
                } else if sections_not_observed {
                    "sections_not_observed: no sectionValue or cocycleValue observation covers any selected Cech edge"
                } else {
                    "selected cover has a non-empty Cech 1-skeleton for ag.cech-obstruction"
                },
                "observedEdgeCount": observed_edges.len(),
                "unobservedEdgeRefs": unobserved_edge_refs,
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
                    "dimension": if empty_selected_scope || cover_nerve_face_count > 0 {
                        Value::Null
                    } else {
                        json!(0)
                    },
                    "status": if empty_selected_scope {
                        "not_computed"
                    } else if cover_nerve_face_count == 0 {
                        "computed_for_selected_1_skeleton"
                    } else {
                        "not_measured_for_triple_overlap_faces"
                    },
                    "reason": if empty_selected_scope {
                        "empty_selected_scope: selected cover has no non-empty Cech 1-skeleton for ag.cech-obstruction"
                    } else if cover_nerve_face_count == 0 {
                        "no selected 2-simplices are present in the finite incidence graph complex"
                    } else {
                        "triple-overlap faces are projected for viewer geometry only; H2 coherence remains outside this measurement"
                    }
                },
                "observedCocycle": {
                    "classNonzero": h1_class_nonzero,
                    "representative": representative,
                    "mismatchSupportRefs": mismatch_support_refs
                },
                "classSupport": {
                    "kind": "selected-cover-edge-support",
                    "edgeRefs": edges.iter()
                        .filter(|edge| edge.value == 1)
                        .map(|edge| edge.edge_id.clone())
                        .collect::<Vec<_>>(),
                    "supportAtomRefs": mismatch_support_refs
                },
                "nerveShape": {
                    "b1": if empty_selected_scope {
                        Value::Null
                    } else {
                        json!(nerve_complex_b1_f2(&selected_contexts, &edges, &cover_nerve_projection))
                    },
                    "oneSkeletonB1": if empty_selected_scope {
                        Value::Null
                    } else {
                        json!(h1_dimension)
                    },
                    "capacityLowerBound": topological_debt_capacity["capacityLowerBound"].clone(),
                    "isForest": if empty_selected_scope {
                        Value::Null
                    } else {
                        json!(nerve_is_forest)
                    },
                    "eulerCharacteristic": topological_debt_capacity["eulerCharacteristic"].clone()
                },
                "theorem12_4Discharge": {
                    "theoremRef": "part4/12.4",
                    "isForest": discharged_check_json(nerve_is_forest, "selected-cover graph cycle rank is zero"),
                    "tripleOverlapsEmpty": discharged_check_json(!has_triple_overlap_faces, "selected cover has no projected triple-overlap faces"),
                    "restrictionMapsSurjective": discharged_check_json(restriction_surjectivity_checked, "explicit restrictionSurjectivityWitness atoms cover every selected restriction edge"),
                    "restrictionSurjectivityWitnesses": restriction_surjectivity_witnesses,
                    "coverShapeExcludesGluingObstruction": cover_shape_excludes_gluing_obstruction,
                    "conclusionCode": if cover_shape_excludes_gluing_obstruction {
                        Value::String(ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION.to_string())
                    } else {
                        Value::Null
                    }
                },
                "boundaryNote": "COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION is relative to the selected abelian coefficient sheaf; non-abelian torsor, stacky descent, and gerbe obstructions are not excluded."
            }),
            topological_debt_capacity,
        ],
        assumptions,
    }
}

fn topological_debt_capacity_invariant_v1(
    profile: &MeasurementProfileV1,
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    cover_nerve_projection: &Value,
    one_skeleton_b1: usize,
    h1_class_nonzero: bool,
    empty_selected_scope: bool,
) -> Value {
    let dim_c0 = selected_contexts.len();
    let dim_c1 = edges.len();
    let dim_c2 = cover_nerve_projection["faces"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let raw_capacity = dim_c1 as isize - dim_c0 as isize - dim_c2 as isize;
    let capacity_lower_bound = raw_capacity.max(0) as usize;
    let euler_characteristic = dim_c0 as isize - dim_c1 as isize + dim_c2 as isize;
    let nerve_complex_b1 = nerve_complex_b1_f2(selected_contexts, edges, cover_nerve_projection);
    json!({
        "invariantId": format!("topological-debt-capacity:{}", profile.profile_id),
        "evaluator": "ag.cech-obstruction",
        "method": "finite-f2-rank-nullity-nerve-capacity@1",
        "status": if empty_selected_scope {
            "not_computed"
        } else {
            "computed"
        },
        "methodStatus": if empty_selected_scope {
            "empty_selected_scope"
        } else {
            "finite_f2_nerve_capacity_computed"
        },
        "selectedCoverRef": profile.cover_ref,
        "coefficient": profile.coefficient,
        "dimensions": {
            "dimC0": dim_c0,
            "dimC1": dim_c1,
            "dimC2": dim_c2
        },
        "capacityLowerBound": if empty_selected_scope {
            Value::Null
        } else {
            json!(capacity_lower_bound)
        },
        "capacityFormula": "max(0, dimC1 - dimC0 - dimC2)",
        "eulerCharacteristic": if empty_selected_scope {
            Value::Null
        } else {
            json!(euler_characteristic)
        },
        "eulerFormula": "dimC0 - dimC1 + dimC2",
        "b1NerveReading": {
            "oneSkeletonB1": if empty_selected_scope {
                Value::Null
            } else {
                json!(one_skeleton_b1)
            },
            "nerveComplexB1": if empty_selected_scope {
                Value::Null
            } else {
                json!(nerve_complex_b1)
            },
            "oneSkeletonMethod": "graph-cycle-rank@1",
            "nerveComplexMethod": "finite-f2-simplicial-homology-with-selected-2-faces@1",
            "distinction": "oneSkeletonB1 counts graph cycles before selected triple-overlap faces are quotiented; nerveComplexB1 includes those faces and may be smaller.",
            "nonClaim": "capacityLowerBound and b1NerveReading are capacity/accounting readings, not new structural verdicts and not concrete H1 class existence claims."
        },
        "measuredCechVerdictEcho": {
            "evaluator": "ag.cech-obstruction",
            "certRef": if empty_selected_scope {
                Value::Null
            } else {
                json!(format!("computedInvariants/cech-cohomology:{}", profile.profile_id))
            },
            "h1ClassNonzero": h1_class_nonzero,
            "note": "This is an echo of the separate Cech structural verdict, not a capacity-derived class claim."
        },
        "boundaryNote": "Part IV principle 11.3 is referenced only as the Cohomological Non-Claim boundary; this row does not import any Part VII numbering or create a viewer verdict.",
        "structuralVerdictRef": Value::Null
    })
}

fn nerve_complex_b1_f2(
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    cover_nerve_projection: &Value,
) -> usize {
    let mut simplices = selected_contexts
        .iter()
        .map(|context| vec![context.clone()])
        .collect::<Vec<_>>();
    simplices.extend(
        edges
            .iter()
            .map(|edge| sorted_simplex([edge.source_context.clone(), edge.target_context.clone()])),
    );
    if let Some(faces) = cover_nerve_projection["faces"].as_array() {
        for face in faces {
            let contexts = face["contextRefs"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|value| value.as_str().map(ToOwned::to_owned))
                .collect::<Vec<_>>();
            if contexts.len() < 3 {
                continue;
            }
            let edge_refs = face["edgeRefs"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|value| value.as_str())
                .collect::<BTreeSet<_>>();
            if edge_refs.len() == 3 {
                simplices.push(sorted_simplex(contexts));
            }
        }
    }
    simplices.sort();
    simplices.dedup();
    reduced_simplicial_homology_f2(&simplices)
        .into_iter()
        .find(|row| row["degree"] == 1)
        .and_then(|row| row["dimension"].as_u64())
        .unwrap_or(0) as usize
}

fn sorted_simplex(items: impl IntoIterator<Item = String>) -> Vec<String> {
    let mut simplex = items.into_iter().collect::<Vec<_>>();
    simplex.sort();
    simplex.dedup();
    simplex
}

fn cech_effectivity_assumptions_v1(
    profile: &MeasurementProfileV1,
    nerve_is_forest: bool,
    has_triple_overlap_faces: bool,
    restriction_surjectivity_checked: bool,
) -> Vec<AgAssumptionLedgerEntryV1> {
    let profile_ref = format!("measurement-profile:{}", profile.profile_id);
    let forest_checked = nerve_is_forest && !has_triple_overlap_faces;
    let forest_checked_by = forest_checked.then(|| {
        format!(
            "cover-nerve:{}:forest=true:no-triple-overlap-faces=true",
            profile.cover_ref
        )
    });
    let forest_assumed_by = (!forest_checked).then(|| profile_ref.clone());

    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/11.1".to_string(),
            assumption: "local lawful sections form an effective Ob_U-torsor".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(profile_ref.clone()),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/11.1".to_string(),
            assumption: "local adjustment action is fixed and effective".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(profile_ref.clone()),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/11.1".to_string(),
            assumption: "coefficient object satisfies descent".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(profile_ref.clone()),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/12.4".to_string(),
            assumption: "restriction maps are surjective".to_string(),
            status: if restriction_surjectivity_checked {
                "checked"
            } else {
                "assumed"
            }
            .to_string(),
            checked_by: restriction_surjectivity_checked.then(|| {
                format!(
                    "cover-nerve:{}:restrictionSurjectivityWitness=all-selected-edges",
                    profile.cover_ref
                )
            }),
            assumed_by: (!restriction_surjectivity_checked).then(|| profile_ref.clone()),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/12.4".to_string(),
            assumption: "selected Cech nerve is a forest with no triple-overlap faces".to_string(),
            status: if forest_checked { "checked" } else { "assumed" }.to_string(),
            checked_by: forest_checked_by,
            assumed_by: forest_assumed_by,
        },
    ]
}

fn discharged_check_json(holds: bool, checked_by: &str) -> Value {
    json!({
        "holds": holds,
        "status": if holds {
            "discharged_by_check"
        } else {
            "not_discharged"
        },
        "checkedBy": if holds {
            Value::String(checked_by.to_string())
        } else {
            Value::Null
        }
    })
}

fn restriction_surjectivity_witnesses_v1(
    normalized: &NormalizedArchMapV2,
    edges: &[CechEdgeV1],
) -> Vec<Value> {
    let edge_ids = edges
        .iter()
        .map(|edge| edge.edge_id.as_str())
        .collect::<BTreeSet<_>>();
    normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "cech"
                && atom.predicate == "restrictionSurjectivityWitness"
                && edge_ids.contains(atom.subject.as_str())
        })
        .map(|atom| {
            json!({
                "edgeRef": atom.subject,
                "atomRef": atom.normalized_atom_id,
                "sourceRefs": atom.source_refs
            })
        })
        .collect()
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
                "ag.cech-obstruction requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if !profile
        .witness_family
        .iter()
        .any(|witness| witness.law == "ag.cech-obstruction")
    {
        return Err(format!(
            "ag.cech-obstruction requires law-surface witness variables for law ag.cech-obstruction",
        ));
    }
    Ok(())
}

fn validate_restriction_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "F2"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-support-inclusion@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "support-inclusion@1",
        ),
        ("domain", profile.domain.as_str(), "finite-poset-site"),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "all-inclusions-hold@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "some-inclusion-fails@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
        (
            "verdictDiscipline",
            profile.verdict_discipline.as_str(),
            "five-valued-structural-verdict@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.restriction-compatibility requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if !profile
        .witness_family
        .iter()
        .any(|witness| witness.law == "ag.restriction-compatibility")
    {
        return Err(
            "ag.restriction-compatibility requires law-surface witness variables for law ag.restriction-compatibility"
                .to_string(),
        );
    }
    Ok(())
}

fn validate_section_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "F2"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-section-evaluation@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "section-factorization@1",
        ),
        ("domain", profile.domain.as_str(), "finite-poset-site"),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "pullback-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "pullback-nonzero@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
        (
            "verdictDiscipline",
            profile.verdict_discipline.as_str(),
            "five-valued-structural-verdict@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.section-factorization requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if section_witness_variables(profile).is_empty() {
        return Err(
            "ag.section-factorization requires law-surface witness variables for law ag.section-factorization"
                .to_string(),
        );
    }
    if section_witness_variables(profile).len() > MAX_SQUARE_FREE_WITNESS_VARIABLES {
        return Err(format!(
            "ag.section-factorization supports at most {MAX_SQUARE_FREE_WITNESS_VARIABLES} witness variables for finite support enumeration"
        ));
    }
    if section_witness_variables(profile).len()
        > profile.finite_bounds.max_square_free_witness_variables
    {
        return Err(format!(
            "ag.section-factorization witness variables exceed MeasurementProfile finiteBounds.maxSquareFreeWitnessVariables={}",
            profile.finite_bounds.max_square_free_witness_variables
        ));
    }
    Ok(())
}

fn validate_coherence_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "h2-coherence@1",
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
                "ag.coherence-obstruction requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if !profile
        .witness_family
        .iter()
        .any(|witness| witness.law == "ag.coherence-obstruction")
    {
        return Err(format!(
            "ag.coherence-obstruction requires law-surface witness variables for law ag.coherence-obstruction",
        ));
    }
    Ok(())
}

fn validate_boundary_residue_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-mayer-vietoris-d0@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "boundary-residue-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "boundary-residue-nonzero@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
        ("domain", profile.domain.as_str(), "finite-poset-site"),
        (
            "verdictDiscipline",
            profile.verdict_discipline.as_str(),
            "five-valued-structural-verdict@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.boundary-residue requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if profile.resolution_selector != "mayer-vietoris-d0@1" {
        return Err(format!(
            "ag.boundary-residue requires MeasurementProfile resolutionSelector=mayer-vietoris-d0@1, found {}",
            profile.resolution_selector
        ));
    }
    if boundary_residue_witness_variables(profile).is_empty() {
        return Err(format!(
            "ag.boundary-residue requires law-surface witness variables for law ag.boundary-residue",
        ));
    }
    if boundary_residue_witness_variables(profile).len() > MAX_BOUNDARY_RESIDUE_VARIABLES {
        return Err(format!(
            "ag.boundary-residue supports at most {MAX_BOUNDARY_RESIDUE_VARIABLES} witness variables for finite F2 image membership"
        ));
    }
    if boundary_residue_witness_variables(profile).len()
        > profile.finite_bounds.max_boundary_residue_variables
    {
        return Err(format!(
            "ag.boundary-residue witness variables exceed MeasurementProfile finiteBounds.maxBoundaryResidueVariables={}",
            profile.finite_bounds.max_boundary_residue_variables
        ));
    }
    Ok(())
}

fn validate_square_free_profile_v1(
    profile: &MeasurementProfileV1,
    witness_variables: &[String],
) -> Result<(), String> {
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
                "ag.square-free-repair requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if witness_variables.is_empty() {
        return Err(format!(
            "ag.square-free-repair requires law surface witness variables for {}",
            profile.profile_id,
        ));
    }
    if witness_variables.len() > MAX_SQUARE_FREE_WITNESS_VARIABLES {
        return Err(format!(
            "ag.square-free-repair supports at most {MAX_SQUARE_FREE_WITNESS_VARIABLES} witness variables for finite support enumeration"
        ));
    }
    if witness_variables.len() > profile.finite_bounds.max_square_free_witness_variables {
        return Err(format!(
            "ag.square-free-repair witness variables exceed MeasurementProfile finiteBounds.maxSquareFreeWitnessVariables={}",
            profile.finite_bounds.max_square_free_witness_variables
        ));
    }
    Ok(())
}

fn validate_tor_profile_v1(
    profile: &MeasurementProfileV1,
    witness_variables: &[String],
) -> Result<(), String> {
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
                "ag.law-conflict-tor requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if profile.resolution_selector != "taylor@1" {
        return Err(format!(
            "ag.law-conflict-tor requires MeasurementProfile resolutionSelector=taylor@1, found {}",
            profile.resolution_selector
        ));
    }
    if witness_variables.is_empty() {
        return Err(format!(
            "ag.law-conflict-tor requires law surface witness variables for {}",
            profile.profile_id
        ));
    }
    if witness_variables.len() > MAX_TOR_WITNESS_VARIABLES {
        return Err(format!(
            "ag.law-conflict-tor supports at most {MAX_TOR_WITNESS_VARIABLES} witness variables for finite monomial enumeration"
        ));
    }
    if witness_variables.len() > profile.finite_bounds.max_tor_witness_variables {
        return Err(format!(
            "ag.law-conflict-tor witness variables exceed MeasurementProfile finiteBounds.maxTorWitnessVariables={}",
            profile.finite_bounds.max_tor_witness_variables
        ));
    }
    Ok(())
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
                "ag.sheaf-laplacian requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if laplacian_witness_variables(profile).is_empty() {
        return Err(format!(
            "ag.sheaf-laplacian requires law-surface witness variables for law ag.sheaf-laplacian",
        ));
    }
    if laplacian_witness_variables(profile).len() > MAX_LAPLACIAN_CELLS {
        return Err(format!(
            "ag.sheaf-laplacian supports at most {MAX_LAPLACIAN_CELLS} witness cells for finite Laplacian enumeration"
        ));
    }
    if laplacian_witness_variables(profile).len() > profile.finite_bounds.max_laplacian_cells {
        return Err(format!(
            "ag.sheaf-laplacian witness cells exceed MeasurementProfile finiteBounds.maxLaplacianCells={}",
            profile.finite_bounds.max_laplacian_cells
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
                "ag.period-stokes requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if period_witness_cycles(profile).is_empty() {
        return Err(format!(
            "ag.period-stokes requires law-surface witness variables for law ag.period-stokes",
        ));
    }
    if period_witness_cycles(profile).len() > MAX_PERIOD_CYCLES {
        return Err(format!(
            "ag.period-stokes supports at most {MAX_PERIOD_CYCLES} witness cycles for finite period enumeration"
        ));
    }
    if period_witness_cycles(profile).len() > profile.finite_bounds.max_period_cycles {
        return Err(format!(
            "ag.period-stokes witness cycles exceed MeasurementProfile finiteBounds.maxPeriodCycles={}",
            profile.finite_bounds.max_period_cycles
        ));
    }
    Ok(())
}

fn validate_period_audit_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "fixed-coefficient-stokes-audit@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "finite-poset-period-stokes-audit@1",
        ),
        ("domain", profile.domain.as_str(), "finite-poset-site"),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "stokes-residual-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "stokes-residual-nonzero@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
        (
            "verdictDiscipline",
            profile.verdict_discipline.as_str(),
            "five-valued-structural-verdict@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.period-stokes-audit requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if !matches!(profile.coefficient.as_str(), "F2" | "Q" | "R") {
        return Err(format!(
            "ag.period-stokes-audit requires MeasurementProfile coefficient F2, Q, or R, found {}",
            profile.coefficient
        ));
    }
    if period_audit_witness_cycles(profile).is_empty() {
        return Err(format!(
            "ag.period-stokes-audit requires law-surface witness variables for law ag.period-stokes-audit",
        ));
    }
    if period_audit_witness_cycles(profile).len() > MAX_PERIOD_CYCLES {
        return Err(format!(
            "ag.period-stokes-audit supports at most {MAX_PERIOD_CYCLES} witness cycles for finite period enumeration"
        ));
    }
    if period_audit_witness_cycles(profile).len() > profile.finite_bounds.max_period_cycles {
        return Err(format!(
            "ag.period-stokes-audit witness cycles exceed MeasurementProfile finiteBounds.maxPeriodCycles={}",
            profile.finite_bounds.max_period_cycles
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
                "ag.support-transfer requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if transfer_witness_targets(profile).is_empty() {
        return Err(format!(
            "ag.support-transfer requires law-surface witness variables for law ag.support-transfer",
        ));
    }
    if transfer_witness_targets(profile).len() > MAX_TRANSFER_TARGETS {
        return Err(format!(
            "ag.support-transfer supports at most {MAX_TRANSFER_TARGETS} witness targets for finite transfer enumeration"
        ));
    }
    if transfer_witness_targets(profile).len() > profile.finite_bounds.max_transfer_targets {
        return Err(format!(
            "ag.support-transfer witness targets exceed MeasurementProfile finiteBounds.maxTransferTargets={}",
            profile.finite_bounds.max_transfer_targets
        ));
    }
    Ok(())
}

fn laplacian_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| {
            matches!(
                witness.law.as_str(),
                "ag.sheaf-laplacian" | "ag.harmonic-debt"
            )
        })
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

fn period_audit_witness_cycles(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.period-stokes-audit")
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
                "ag.sheaf-laplacian cochain {} uses cell outside law-surface witness variables: {}",
                atom.normalized_atom_id, atom.subject
            ));
        }
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.sheaf-laplacian cochain {} requires numeric object",
                atom.normalized_atom_id
            )
        })?;
        let value = raw.parse::<f64>().map_err(|_| {
            format!(
                "ag.sheaf-laplacian cochain {} has non-numeric object {raw}",
                atom.normalized_atom_id
            )
        })?;
        if !value.is_finite() {
            return Err(format!(
                "ag.sheaf-laplacian cochain {} requires finite numeric object",
                atom.normalized_atom_id
            ));
        }
        if cells
            .iter()
            .any(|cell: &LaplacianCellV1| cell.cell_id == atom.subject)
        {
            return Err(format!(
                "ag.sheaf-laplacian duplicate cellular cochain for {}",
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
                "ag.sheaf-laplacian boundary {} requires target cell object",
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
                "ag.period-stokes period integral {} requires object cycle=value",
                atom.normalized_atom_id
            )
        })?;
        let (cycle_id, value) = parse_numeric_assignment(
            raw,
            "ag.period-stokes period integral",
            &atom.normalized_atom_id,
        )?;
        if !cycle_set.contains(&cycle_id) {
            return Err(format!(
                "ag.period-stokes period integral {} uses cycle outside law-surface witness variables: {}",
                atom.normalized_atom_id, cycle_id
            ));
        }
        if pairings.iter().any(|pairing: &PeriodIntegralV1| {
            pairing.form_id == atom.subject && pairing.cycle_id == cycle_id
        }) {
            return Err(format!(
                "ag.period-stokes duplicate period integral for form {} and cycle {}",
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
            "ag.period-stokes Stokes audit requires matching dOmegaIntegral and boundaryPeriod keys"
                .to_string(),
        );
    }
    let mut max_abs_residual: f64 = 0.0;
    let mut pairs = Vec::new();
    for (key, left) in d_map {
        let right = boundary_map[&key];
        let residual = left.value - right.value;
        max_abs_residual = max_abs_residual.max(residual.abs());
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
        "status": if max_abs_residual > 1.0e-9 {
            "residual_nonzero"
        } else {
            "checked"
        },
        "maxAbsoluteResidual": round_f64(max_abs_residual),
        "pairs": pairs
    }))
}

fn fixed_coefficient_stokes_audit_report(
    d_omega: &[StokesAuditValueV1],
    boundary: &[StokesAuditValueV1],
    coefficient: &str,
) -> Value {
    if !matches!(coefficient, "F2" | "Q") {
        return json!({
            "identity": "<d omega, gamma> = <omega, boundary gamma>",
            "status": "unknown",
            "methodStatus": "strict_coefficient_unresolved",
            "coefficient": coefficient,
            "reason": "strict coefficient ring is unresolved; float/model-relative period data remains analytic-only",
            "pairs": []
        });
    }
    if d_omega.is_empty() || boundary.is_empty() {
        return json!({
            "identity": "<d omega, gamma> = <omega, boundary gamma>",
            "status": "not_computed",
            "methodStatus": "period_audit_model_missing",
            "coefficient": coefficient,
            "reason": "period Stokes audit requires non-empty dOmegaIntegral and boundaryPeriod values",
            "pairs": []
        });
    }
    let d_map = d_omega
        .iter()
        .map(|entry| ((entry.form_id.clone(), entry.chain_id.clone()), entry))
        .collect::<BTreeMap<_, _>>();
    let boundary_map = boundary
        .iter()
        .map(|entry| ((entry.form_id.clone(), entry.chain_id.clone()), entry))
        .collect::<BTreeMap<_, _>>();
    if d_map.keys().collect::<Vec<_>>() != boundary_map.keys().collect::<Vec<_>>() {
        return json!({
            "identity": "<d omega, gamma> = <omega, boundary gamma>",
            "status": "not_computed",
            "methodStatus": "period_audit_key_mismatch",
            "coefficient": coefficient,
            "reason": "period Stokes audit requires matching dOmegaIntegral and boundaryPeriod keys",
            "pairs": []
        });
    }

    let mut nonzero_count = 0usize;
    let mut max_abs_residual = 0.0f64;
    let mut pairs = Vec::new();
    for (key, left) in d_map {
        let right = boundary_map[&key];
        let Some(residual) = fixed_coefficient_residual(left.value, right.value, coefficient)
        else {
            return json!({
                "identity": "<d omega, gamma> = <omega, boundary gamma>",
                "status": "unknown",
                "methodStatus": "strict_coefficient_unresolved",
                "coefficient": coefficient,
                "reason": "fixed coefficient Stokes audit requires exact Q values or integer F2 representatives",
                "pairs": []
            });
        };
        if residual.abs() > 1.0e-9 {
            nonzero_count += 1;
        }
        max_abs_residual = max_abs_residual.max(residual.abs());
        pairs.push(json!({
            "form": left.form_id,
            "chain": left.chain_id,
            "dOmegaIntegral": fixed_coefficient_value(left.value, coefficient),
            "boundaryPeriod": fixed_coefficient_value(right.value, coefficient),
            "residual": fixed_coefficient_value(residual, coefficient),
            "dOmegaAtomRef": left.atom_ref,
            "boundaryAtomRef": right.atom_ref
        }));
    }
    json!({
        "identity": "<d omega, gamma> = <omega, boundary gamma>",
        "status": if nonzero_count == 0 {
            "checked"
        } else {
            "residual_nonzero"
        },
        "methodStatus": "fixed_coefficient_stokes_audit_computed",
        "coefficient": coefficient,
        "maxAbsoluteResidual": fixed_coefficient_value(max_abs_residual, coefficient),
        "nonzeroPairCount": nonzero_count,
        "pairs": pairs
    })
}

fn fixed_coefficient_residual(left: f64, right: f64, coefficient: &str) -> Option<f64> {
    match coefficient {
        "F2" => {
            let left_int = f2_integer_representative(left)?;
            let right_int = f2_integer_representative(right)?;
            Some(((left_int - right_int).rem_euclid(2)) as f64)
        }
        "Q" => Some(round_f64(left - right)),
        _ => None,
    }
}

fn f2_integer_representative(value: f64) -> Option<i64> {
    if !value.is_finite() {
        return None;
    }
    let rounded = value.round();
    ((value - rounded).abs() < 1.0e-9).then_some(rounded as i64)
}

fn fixed_coefficient_value(value: f64, coefficient: &str) -> Value {
    if coefficient == "F2" {
        json!(f2_integer_representative(value).unwrap_or(0).rem_euclid(2))
    } else {
        json!(round_f64(value))
    }
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
                "ag.support-transfer transfer pairing {} requires object target=value",
                atom.normalized_atom_id
            )
        })?;
        let (target_id, value) = parse_numeric_assignment(
            raw,
            "ag.support-transfer transfer pairing",
            &atom.normalized_atom_id,
        )?;
        if !target_set.contains(&target_id) {
            return Err(format!(
                "ag.support-transfer transfer pairing {} uses target outside law-surface witness variables: {}",
                atom.normalized_atom_id, target_id
            ));
        }
        if pairings.iter().any(|pairing: &TransferPairingV1| {
            pairing.path_id == atom.subject && pairing.target_id == target_id
        }) {
            return Err(format!(
                "ag.support-transfer duplicate transfer pairing for path {} and target {}",
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
    targets: &[String],
) -> Result<Vec<TransferRepairPathV1>, String> {
    let target_set = targets.iter().cloned().collect::<BTreeSet<_>>();
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
                "ag.support-transfer duplicate repair path {}",
                atom.subject
            ));
        }
        let support_targets = atom
            .object
            .as_deref()
            .map(parse_csv_values)
            .unwrap_or_default()
            .into_iter()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let unknown_support_targets = support_targets
            .iter()
            .filter(|target| !target_set.contains(*target))
            .cloned()
            .collect::<Vec<_>>();
        if !unknown_support_targets.is_empty() {
            return Err(format!(
                "ag.support-transfer repair path {} uses support targets outside law-surface witness variables: {}",
                atom.normalized_atom_id,
                unknown_support_targets.join(",")
            ));
        }
        paths.push(TransferRepairPathV1 {
            path_id: atom.subject.clone(),
            support_targets,
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
                "ag.support-transfer ground cost {} uses target outside law-surface witness variables: {}",
                atom.normalized_atom_id, atom.subject
            ));
        }
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.support-transfer ground cost {} requires numeric object",
                atom.normalized_atom_id
            )
        })?;
        let cost = raw.parse::<f64>().map_err(|_| {
            format!(
                "ag.support-transfer ground cost {} has non-numeric object {raw}",
                atom.normalized_atom_id
            )
        })?;
        if !cost.is_finite() || cost < 0.0 {
            return Err(format!(
                "ag.support-transfer ground cost {} requires finite non-negative object",
                atom.normalized_atom_id
            ));
        }
        if costs
            .iter()
            .any(|cost_entry: &TransferGroundCostV1| cost_entry.target_id == atom.subject)
        {
            return Err(format!(
                "ag.support-transfer duplicate ground cost for target {}",
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
            assumption:
                "finite cellular measurement model selected by supplied law-equation-surface"
                    .to_string(),
            status: cellular_model_status.to_string(),
            checked_by: (cellular_model_status == "checked")
                .then(|| "law-surface:provided-law-equation-surface".to_string()),
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
            assumption: "finite poset period model selected by supplied law-equation-surface"
                .to_string(),
            status: period_model_status.to_string(),
            checked_by: (period_model_status == "checked")
                .then(|| "law-surface:provided-law-equation-surface".to_string()),
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

fn period_audit_assumptions(
    profile: &MeasurementProfileV1,
    fixed_coefficient_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/13.2".to_string(),
            assumption:
                "supplied finite Stokes accounting values share a fixed coefficient reading"
                    .to_string(),
            status: fixed_coefficient_status.to_string(),
            checked_by: (fixed_coefficient_status == "checked").then(|| {
                format!(
                    "measurement-profile:{}.coefficient={}",
                    profile.profile_id, profile.coefficient
                )
            }),
            assumed_by: (fixed_coefficient_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part7/5.2A".to_string(),
            assumption: "strict-period-pairing remains analytic and model-relative".to_string(),
            status: "checked".to_string(),
            checked_by: Some("strict-period-pairing@1".to_string()),
            assumed_by: None,
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
            assumption:
                "finite support-localized transfer model selected by supplied law-equation-surface"
                    .to_string(),
            status: transfer_model_status.to_string(),
            checked_by: (transfer_model_status == "checked")
                .then(|| "law-surface:provided-law-equation-surface".to_string()),
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

fn coherence_assumptions(
    profile: &MeasurementProfileV1,
    coefficient_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/10.1".to_string(),
            assumption: "banded abelian F2 coefficient object for selected H2 coherence"
                .to_string(),
            status: coefficient_status.to_string(),
            checked_by: (coefficient_status == "checked").then(|| {
                format!(
                    "measurement-profile:{}.coefficient={}",
                    profile.profile_id, profile.coefficient
                )
            }),
            assumed_by: (coefficient_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/10.1".to_string(),
            assumption: "selected cover supplies a finite triple-overlap 2-skeleton".to_string(),
            status: "checked".to_string(),
            checked_by: Some(format!(
                "measurement-profile:{}.coverRef",
                profile.profile_id
            )),
            assumed_by: None,
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/B.8.2".to_string(),
            assumption:
                "Leray / acyclicity comparison from selected Cech complex to sheaf cohomology"
                    .to_string(),
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
                    "ag.law-conflict-tor common ambient {} requires object law pair",
                    atom.normalized_atom_id
                )
            })?;
            let law_pair = raw_pair
                .split(',')
                .map(str::trim)
                .filter(|law| !law.is_empty())
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            let unique_laws = law_pair.iter().cloned().collect::<BTreeSet<_>>();
            if law_pair.len() != 2 || unique_laws.len() != 2 {
                return Err(format!(
                    "ag.law-conflict-tor common ambient {} requires exactly two laws in object",
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
            "ag.law-conflict-tor expected at most one selected common ambient, found {}",
            ambients.len()
        ));
    }

    Ok(ambients.into_iter().next())
}

fn tor_ideal_generators(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    laws: &[&crate::LawEquationV1],
    witness_variables: &[String],
) -> Result<Vec<TorIdealGeneratorV1>, String> {
    let observations = normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "tor" && atom.predicate == "lawIdealGenerator")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .collect::<Vec<_>>();
    let observed_laws = observations
        .iter()
        .map(|atom| atom.subject.clone())
        .collect::<BTreeSet<_>>();
    let declared_law_ids = laws
        .iter()
        .map(|law| law.law_id.as_str())
        .collect::<BTreeSet<_>>();
    let outside_laws = observed_laws
        .iter()
        .filter(|law| !declared_law_ids.contains(law.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    if !outside_laws.is_empty() {
        return Err(format!(
            "ag.law-conflict-tor observed law generators outside supplied law surface: {}",
            outside_laws.join(",")
        ));
    }
    let mut generators = Vec::new();
    for law in laws {
        let (_, law_aliases, binding_axis, binding_predicate) = law_witness_bindings(law)?;
        let (observed_axis, observed_predicate) =
            observation_selector("tor", &binding_axis, &binding_predicate)?;
        let declared_supports = declared_law_supports(law, witness_variables)?;
        if !observed_laws.contains(&law.law_id) {
            continue;
        }
        for (index, support) in declared_supports.iter().enumerate() {
            let matching_atoms = observations
                .iter()
                .filter(|atom| atom.subject == law.law_id)
                .filter(|atom| {
                    observed_support_matches(
                        atom,
                        support,
                        &law_aliases,
                        observed_axis,
                        observed_predicate,
                    )
                })
                .collect::<Vec<_>>();
            if matching_atoms.is_empty() {
                continue;
            }
            let context_refs = matching_atoms
                .iter()
                .flat_map(|atom| atom.context_memberships.iter().cloned())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            let source_refs = matching_atoms
                .iter()
                .flat_map(|atom| atom.source_refs.iter().cloned())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            let square_free = matching_atoms
                .iter()
                .all(|atom| observed_tor_support_is_square_free(atom));
            generators.push(TorIdealGeneratorV1 {
                law: law.law_id.clone(),
                generator_id: format!("law-surface:{}:{}", law.law_id, index + 1),
                support: support.clone(),
                square_free,
                context_refs,
                source_refs,
            });
        }
    }
    generators.sort_by(|left, right| {
        left.law
            .cmp(&right.law)
            .then_with(|| left.generator_id.cmp(&right.generator_id))
    });
    Ok(generators)
}

fn tor_shared_support_proxy_classes(
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
                multidegree: support.clone(),
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

fn tor_taylor_h1_classes(
    generators: &[TorIdealGeneratorV1],
    left_law: &str,
    right_law: &str,
    witness_variables: &[String],
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

    for multidegree in all_subsets(witness_variables)
        .into_iter()
        .filter(|degree| !degree.is_empty())
    {
        let f1_basis = left_generators
            .iter()
            .filter(|generator| is_subset(&generator.support, &multidegree))
            .filter(|generator| {
                let factor = support_difference(&multidegree, &generator.support);
                !monomial_zero_in_quotient(&factor, &right_generators)
            })
            .copied()
            .collect::<Vec<_>>();
        if f1_basis.is_empty() {
            continue;
        }

        let target_zero = monomial_zero_in_quotient(&multidegree, &right_generators);
        let rank_d1 = if target_zero { 0 } else { 1 };
        let kernel_dim = f1_basis.len().saturating_sub(rank_d1);
        if kernel_dim == 0 {
            continue;
        }

        let f1_index = f1_basis
            .iter()
            .enumerate()
            .map(|(index, generator)| (generator.generator_id.clone(), index))
            .collect::<BTreeMap<_, _>>();
        let mut d2_columns = Vec::new();
        for left_index in 0..left_generators.len() {
            for right_index in (left_index + 1)..left_generators.len() {
                let first = left_generators[left_index];
                let second = left_generators[right_index];
                let lcm = support_union(&first.support, &second.support);
                if !is_subset(&lcm, &multidegree) {
                    continue;
                }
                let lcm_factor = support_difference(&multidegree, &lcm);
                if monomial_zero_in_quotient(&lcm_factor, &right_generators) {
                    continue;
                }
                let mut column = vec![0u8; f1_basis.len()];
                if let Some(index) = f1_index.get(&first.generator_id) {
                    column[*index] ^= 1;
                }
                if let Some(index) = f1_index.get(&second.generator_id) {
                    column[*index] ^= 1;
                }
                if column.iter().any(|value| *value == 1) {
                    d2_columns.push(column);
                }
            }
        }
        let rank_d2 = matrix_rank_f2(d2_columns).min(kernel_dim);
        let h1_dim = kernel_dim.saturating_sub(rank_d2);
        if h1_dim == 0 {
            continue;
        }

        let right_witness = right_generators
            .iter()
            .find(|generator| is_subset(&generator.support, &multidegree))
            .copied()
            .or_else(|| right_generators.first().copied());
        let Some(right_witness) = right_witness else {
            continue;
        };
        let left_witnesses = f1_basis
            .iter()
            .map(|generator| generator.generator_id.clone())
            .collect::<Vec<_>>();
        let context_refs = f1_basis
            .iter()
            .flat_map(|generator| generator.context_refs.iter())
            .chain(right_witness.context_refs.iter())
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let source_refs = f1_basis
            .iter()
            .flat_map(|generator| generator.source_refs.iter())
            .chain(right_witness.source_refs.iter())
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let shared_support = f1_basis
            .iter()
            .flat_map(|generator| {
                generator
                    .support
                    .iter()
                    .filter(|variable| right_witness.support.contains(*variable))
                    .cloned()
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();

        for class_index in 0..h1_dim {
            classes.push(TorConflictClassV1 {
                conflict_id: format!("LawConflict_1:{}", classes.len() + 1),
                degree: 1,
                support: multidegree.clone(),
                multidegree: multidegree.clone(),
                shared_support: shared_support.clone(),
                left_law: left_law.to_string(),
                left_generator_ref: left_witnesses
                    .get(class_index)
                    .cloned()
                    .unwrap_or_else(|| left_witnesses.join("+")),
                right_law: right_law.to_string(),
                right_generator_ref: right_witness.generator_id.clone(),
                context_refs: context_refs.clone(),
                source_refs: source_refs.clone(),
            });
        }
    }

    classes.sort_by(|left, right| {
        left.multidegree
            .cmp(&right.multidegree)
            .then_with(|| left.conflict_id.cmp(&right.conflict_id))
    });
    for (index, class) in classes.iter_mut().enumerate() {
        class.conflict_id = format!("LawConflict_1:{}", index + 1);
    }
    classes
}

fn support_union(left: &[String], right: &[String]) -> Vec<String> {
    left.iter()
        .chain(right.iter())
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn support_difference(left: &[String], right: &[String]) -> Vec<String> {
    left.iter()
        .filter(|value| !right.contains(*value))
        .cloned()
        .collect()
}

fn monomial_zero_in_quotient(
    monomial_support: &[String],
    quotient_generators: &[&TorIdealGeneratorV1],
) -> bool {
    quotient_generators
        .iter()
        .any(|generator| is_subset(&generator.support, monomial_support))
}

fn tor_assumptions(
    profile: &MeasurementProfileV1,
    ambient: Option<&TorCommonAmbientV1>,
    ambient_status: &str,
    square_free_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    let coefficient_status = if ambient_status == "checked" {
        "checked"
    } else {
        "violated"
    };

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
            theorem_ref: "part8/9.1-coefficient-compatibility".to_string(),
            assumption:
                "common ambient coefficient compatibility under the selected single F2 coefficient model"
                    .to_string(),
            status: coefficient_status.to_string(),
            checked_by: (coefficient_status == "checked").then(|| {
                format!("measurement-profile:{}.coefficient:F2", profile.profile_id)
            }),
            assumed_by: (coefficient_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part5/5.5".to_string(),
            assumption: "finite square-free monomial law ideals selected for degree-1 Taylor Tor"
                .to_string(),
            status: square_free_status.to_string(),
            checked_by: match square_free_status {
                "checked" => Some(format!(
                    "law-surface:provided-law-equation-surface"
                )),
                "violated" => Some("ag.law-conflict-tor.squareFreeGeneratorCheck".to_string()),
                _ => None,
            },
            assumed_by: (square_free_status == "assumed")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part5/5.5-field".to_string(),
            assumption: "Taylor H1 is computed as an F2 field-coefficient reading".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
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

fn restriction_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    let mut variables = profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.restriction-compatibility")
        .map(|witness| witness.variable.clone())
        .collect::<Vec<_>>();
    variables.sort();
    variables.dedup();
    variables
}

fn restriction_generators(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
) -> Result<Vec<RestrictionGeneratorV1>, String> {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let mut generators = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "restriction-compatibility"
                && atom.predicate == "restrictionIdealGenerator"
        })
        .filter(|atom| selected_contexts.contains(&atom.subject))
    {
        if !atom
            .context_memberships
            .iter()
            .any(|context| context == &atom.subject)
        {
            return Err(format!(
                "ag.restriction-compatibility generator {} must belong to its subject context {}",
                atom.normalized_atom_id, atom.subject
            ));
        }
        let support = restriction_generator_support(atom);
        if support.is_empty() {
            return Err(format!(
                "ag.restriction-compatibility generator {} has no finite support variables",
                atom.normalized_atom_id
            ));
        }
        let unknown = support
            .iter()
            .filter(|variable| !witness_set.contains(*variable))
            .cloned()
            .collect::<Vec<_>>();
        if !unknown.is_empty() {
            return Err(format!(
                "ag.restriction-compatibility generator {} contains variables outside law-surface witness variables: {}",
                atom.normalized_atom_id,
                unknown.join(",")
            ));
        }
        generators.push(RestrictionGeneratorV1 {
            generator_id: atom.normalized_atom_id.clone(),
            context_ref: atom.subject.clone(),
            support,
            source_refs: atom.source_refs.clone(),
        });
    }
    generators.sort_by(|left, right| left.generator_id.cmp(&right.generator_id));
    Ok(generators)
}

fn restriction_generator_support(atom: &NormalizedAtomV2) -> Vec<String> {
    let mut support = atom
        .object
        .as_deref()
        .unwrap_or_default()
        .split(',')
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    support.sort();
    support.dedup();
    support
}

fn restriction_invariant_json(
    profile: &MeasurementProfileV1,
    method_status: &str,
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    witness_variables: &[String],
    edge_checks: &[RestrictionEdgeCheckV1],
) -> Value {
    json!({
        "invariantId": format!("restriction-compatibility:{}", profile.profile_id),
        "evaluator": "ag.restriction-compatibility",
        "method": "finite-support-inclusion@1",
        "status": if method_status == "finite_support_inclusion_computed" { "computed" } else { "not_computed" },
        "methodStatus": method_status,
        "claimScope": "selected-cover separated presheaf restriction compatibility over finite monomial supports",
        "selectedCoverRef": profile.cover_ref,
        "witnessVariables": witness_variables,
        "contextCount": selected_contexts.len(),
        "restrictionEdgeCount": edges.len(),
        "edgeChecks": edge_checks.iter().map(|edge| json!({
            "edgeRef": edge.edge_ref,
            "sourceContextRef": edge.source_context,
            "targetContextRef": edge.target_context,
            "status": edge.status,
            "sourceGenerators": edge.source_generators.iter().map(restriction_generator_json).collect::<Vec<_>>(),
            "targetGenerators": edge.target_generators.iter().map(restriction_generator_json).collect::<Vec<_>>(),
            "violations": edge.violations.iter().map(|violation| json!({
                "generatorRef": violation.generator_id,
                "support": violation.support,
                "sourceRefs": violation.source_refs
            })).collect::<Vec<_>>()
        })).collect::<Vec<_>>(),
        "boundaryNote": "A measured_nonzero row means the selected local-sum presentation does not flow into the target ideal; sheaf image 再定義で消えうる、理論対象の defect ではない.",
        "nonConclusions": [
            "This is a selected-cover separated presheaf check, not a global sheaf or semantic safety proof.",
            "H1 Cech and H2 coherence verdict rows are not changed by this evaluator."
        ]
    })
}

fn restriction_generator_json(generator: &RestrictionGeneratorV1) -> Value {
    json!({
        "generatorId": generator.generator_id,
        "contextRef": generator.context_ref,
        "support": generator.support,
        "sourceRefs": generator.source_refs
    })
}

fn restriction_assumptions(
    profile: &MeasurementProfileV1,
    method_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "Lean/ObstructionIdeal.RestrictionCompatible.maps_selected".to_string(),
            assumption: "selected finite support generator family for restriction compatibility"
                .to_string(),
            status: if method_status == "restriction_generator_missing" {
                "violated"
            } else {
                "checked"
            }
            .to_string(),
            checked_by: (method_status != "restriction_generator_missing")
                .then(|| "law-surface:provided-law-equation-surface".to_string()),
            assumed_by: (method_status == "restriction_generator_missing")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P0-2".to_string(),
            assumption: "selected cover supplies finite restriction edges for support inclusion"
                .to_string(),
            status: if method_status == "empty_selected_restriction_edges" {
                "violated"
            } else {
                "checked"
            }
            .to_string(),
            checked_by: (method_status != "empty_selected_restriction_edges")
                .then(|| format!("measurement-profile:{}.coverRef", profile.profile_id)),
            assumed_by: (method_status == "empty_selected_restriction_edges")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P0-2-boundary".to_string(),
            assumption: "measured nonzero restriction incompatibility is presentation-relative"
                .to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn section_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    let mut variables = profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.section-factorization")
        .map(|witness| witness.variable.clone())
        .collect::<Vec<_>>();
    variables.sort();
    variables.dedup();
    variables
}

fn section_forbidden_supports(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
) -> Result<Vec<SectionForbiddenSupportV1>, String> {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let mut supports = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "section-factorization" && is_raw_support_predicate(atom))
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let support = parse_csv_values(atom.object.as_deref().unwrap_or_default());
        if support.is_empty() {
            return Err(format!(
                "ag.section-factorization raw support {} has no finite support variables",
                atom.normalized_atom_id
            ));
        }
        let unknown = support
            .iter()
            .filter(|variable| !witness_set.contains(*variable))
            .cloned()
            .collect::<Vec<_>>();
        if !unknown.is_empty() {
            return Err(format!(
                "ag.section-factorization raw support {} contains variables outside law-surface witness variables: {}",
                atom.normalized_atom_id,
                unknown.join(",")
            ));
        }
        supports.push(SectionForbiddenSupportV1 {
            support_id: atom.normalized_atom_id.clone(),
            support,
            source_refs: atom.source_refs.clone(),
        });
    }
    supports.sort_by(|left, right| left.support_id.cmp(&right.support_id));
    Ok(supports)
}

fn section_forbidden_supports_from_plan(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
    plan: &LawExecutionPlanV1,
) -> Result<Vec<SectionForbiddenSupportV1>, String> {
    let observed = section_forbidden_supports(normalized, selected_contexts, witness_variables)?;
    let declared = plan
        .section_forbidden_supports
        .as_ref()
        .ok_or_else(|| "section execution plan has no forbidden supports".to_string())?;
    let mut supports = Vec::new();
    for (index, support) in declared.iter().enumerate() {
        let mut observed_support_variables = support
            .iter()
            .map(|variable| {
                plan.section_variable_aliases
                    .as_ref()
                    .and_then(|aliases| aliases.get(variable))
                    .cloned()
                    .unwrap_or_else(|| variable.clone())
            })
            .collect::<Vec<_>>();
        observed_support_variables.sort();
        let mut declared_support = support.clone();
        declared_support.sort();
        let Some(observed_support) = observed
            .iter()
            .find(|candidate| candidate.support == observed_support_variables)
        else {
            return Ok(Vec::new());
        };
        let mut source_refs = observed_support.source_refs.clone();
        source_refs.push(format!("law-surface:{}", plan.surface_id));
        supports.push(SectionForbiddenSupportV1 {
            support_id: format!(
                "law-surface:{}:{}:forbidden:{}",
                plan.surface_id, plan.selected_law_id, index
            ),
            support: declared_support,
            source_refs,
        });
    }
    Ok(supports)
}

fn minimal_section_forbidden_supports(
    supports: &[SectionForbiddenSupportV1],
) -> Vec<SectionForbiddenSupportV1> {
    let minimal = minimal_supports(
        supports
            .iter()
            .map(|support| support.support.clone())
            .collect(),
    );
    minimal
        .into_iter()
        .map(|support| {
            supports
                .iter()
                .filter(|candidate| candidate.support == support)
                .min_by(|left, right| left.support_id.cmp(&right.support_id))
                .cloned()
                .unwrap_or_else(|| SectionForbiddenSupportV1 {
                    support_id: format!("support:{}", support.join("+")),
                    support,
                    source_refs: Vec::new(),
                })
        })
        .collect()
}

fn section_assignment(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
) -> Result<Option<SectionAssignmentV1>, String> {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let atoms = normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "section-factorization" && atom.predicate == "witnessAssignment"
        })
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .collect::<Vec<_>>();
    if atoms.is_empty() {
        return Ok(None);
    }
    if atoms.len() > 1 {
        return Err(format!(
            "ag.section-factorization expects one selected witnessAssignment atom, found {}",
            atoms.len()
        ));
    }
    let atom = atoms[0];
    let mut assigned = BTreeMap::new();
    for field in atom
        .object
        .as_deref()
        .unwrap_or_default()
        .split(',')
        .map(str::trim)
        .filter(|field| !field.is_empty())
    {
        let Some((variable, raw_value)) = field.split_once('=') else {
            return Err(format!(
                "ag.section-factorization witnessAssignment {} segment must be variable=value: {}",
                atom.normalized_atom_id, field
            ));
        };
        let variable = variable.trim().to_string();
        if !witness_set.contains(&variable) {
            return Err(format!(
                "ag.section-factorization witnessAssignment {} contains variable outside law-surface witness variables: {}",
                atom.normalized_atom_id, variable
            ));
        }
        let value = match raw_value.trim() {
            "1" | "true" | "True" => true,
            "0" | "false" | "False" => false,
            other => {
                return Err(format!(
                    "ag.section-factorization witnessAssignment {} has non-Boolean value for {}: {}",
                    atom.normalized_atom_id, variable, other
                ));
            }
        };
        if assigned.insert(variable.clone(), value).is_some() {
            return Err(format!(
                "ag.section-factorization witnessAssignment {} repeats variable {}",
                atom.normalized_atom_id, variable
            ));
        }
    }
    if assigned.is_empty() {
        return Err(format!(
            "ag.section-factorization witnessAssignment {} has no Boolean assignments",
            atom.normalized_atom_id
        ));
    }
    Ok(Some(SectionAssignmentV1 {
        assignment_id: atom.normalized_atom_id.clone(),
        assigned,
        source_refs: atom.source_refs.clone(),
    }))
}

fn section_invariant_json(
    profile: &MeasurementProfileV1,
    method_status: &str,
    witness_variables: &[String],
    forbidden_supports: &[SectionForbiddenSupportV1],
    minimal_forbidden_supports: &[SectionForbiddenSupportV1],
    assignment: Option<&SectionAssignmentV1>,
    assignment_status: &str,
    active_support: &[String],
    violated_supports: &[SectionForbiddenSupportV1],
) -> Value {
    json!({
        "invariantId": format!("section-factorization:{}", profile.profile_id),
        "evaluator": "ag.section-factorization",
        "method": "finite-section-pullback@1",
        "status": if method_status == "finite_section_pullback_computed" { "computed" } else { method_status },
        "methodStatus": method_status,
        "claimScope": "selected Boolean section only; finite s^* I_Ob^U pullback check over the chosen witness family",
        "selectedCoverRef": profile.cover_ref,
        "witnessVariables": witness_variables,
        "obstructionIdeal": {
            "id": "I_Ob^U",
            "generators": forbidden_supports.iter().map(section_support_json).collect::<Vec<_>>()
        },
        "minimalForbiddenSupports": minimal_forbidden_supports.iter().map(section_support_json).collect::<Vec<_>>(),
        "sectionAssignment": assignment.map(|assignment| json!({
            "assignmentRef": assignment.assignment_id,
            "assignmentStatus": assignment_status,
            "assigned": assignment.assigned,
            "activeSupport": active_support,
            "sourceRefs": assignment.source_refs
        })).unwrap_or_else(|| json!({
            "assignmentStatus": "absent",
            "activeSupport": [],
            "sourceRefs": []
        })),
        "violatedForbiddenSupports": violated_supports.iter().map(section_support_json).collect::<Vec<_>>(),
        "boundaryNote": "section-relative lawful only: this finite check does not prove all sections lawful, exactness without No-Cancellation, runtime safety, or semantic safety.",
        "assumptionBoundary": [
            "No-Cancellation/exactness is recorded as assumed, not discharged by ArchSig.",
            "The evaluator reuses measured_zero, measured_nonzero, unknown, and not_computed from the existing five-valued structural verdict vocabulary."
        ]
    })
}

fn section_support_json(support: &SectionForbiddenSupportV1) -> Value {
    json!({
        "supportRef": support.support_id,
        "support": support.support,
        "sourceRefs": support.source_refs
    })
}

fn section_assumptions(
    profile: &MeasurementProfileV1,
    method_status: &str,
    forbidden_supports: &[SectionForbiddenSupportV1],
) -> Vec<AgAssumptionLedgerEntryV1> {
    let support_refs = forbidden_supports
        .iter()
        .map(|support| support.support_id.clone())
        .collect::<Vec<_>>();
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "Lean/FiniteExamples.lawful_iff_factorsThroughLawfulLocus".to_string(),
            assumption: "selected witnessAssignment atom supplies the Boolean section for finite pullback evaluation".to_string(),
            status: if method_status == "section_assignment_absent" {
                "violated"
            } else {
                "checked"
            }
            .to_string(),
            checked_by: (method_status != "section_assignment_absent")
                .then(|| "section-factorization.witnessAssignment".to_string()),
            assumed_by: (method_status == "section_assignment_absent")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P0-3".to_string(),
            assumption: "selected raw support atoms supply the finite I_Ob^U presentation within the selected witness family".to_string(),
            status: if method_status == "obstruction_generators_absent" {
                "violated"
            } else {
                "checked"
            }
            .to_string(),
            checked_by: (!support_refs.is_empty()).then(|| {
                format!(
                    "ag.section-factorization:{}:{}",
                    profile.profile_id,
                    support_refs.join(",")
                )
            }),
            assumed_by: (method_status == "obstruction_generators_absent")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P0-3-boundary".to_string(),
            assumption: "No-Cancellation/exactness boundary for reading s^* I_Ob^U=0 as section-relative lawful".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn boundary_residue_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    let mut variables = profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.boundary-residue")
        .map(|witness| witness.variable.clone())
        .collect::<Vec<_>>();
    variables.sort();
    variables.dedup();
    variables
}

fn boundary_residue_roles(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
) -> Result<Vec<BoundaryResidueRoleV1>, String> {
    let mut roles = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "boundary-residue")
        .filter(|atom| matches!(atom.predicate.as_str(), "patchRole" | "patchClassification"))
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        if !selected_contexts.contains(&atom.subject) {
            return Err(format!(
                "ag.boundary-residue patch role {} subject must be a selected context",
                atom.normalized_atom_id
            ));
        }
        let role = atom.object.as_deref().unwrap_or_default().trim();
        if !matches!(role, "core" | "feature" | "boundary") {
            return Err(format!(
                "ag.boundary-residue patch role {} must be core, feature, or boundary",
                atom.normalized_atom_id
            ));
        }
        roles.push(BoundaryResidueRoleV1 {
            atom_ref: atom.normalized_atom_id.clone(),
            context_ref: atom.subject.clone(),
            role: role.to_string(),
            source_refs: atom.source_refs.clone(),
        });
    }
    roles.sort_by(|left, right| {
        left.role
            .cmp(&right.role)
            .then_with(|| left.context_ref.cmp(&right.context_ref))
    });
    Ok(roles)
}

fn boundary_residue_role_map(roles: &[BoundaryResidueRoleV1]) -> BTreeMap<String, String> {
    let mut role_map = BTreeMap::new();
    for role in roles {
        role_map
            .entry(role.context_ref.clone())
            .and_modify(|existing| {
                if existing != &role.role {
                    *existing = "conflicted".to_string();
                }
            })
            .or_insert_with(|| role.role.clone());
    }
    role_map
}

fn boundary_residue_roles_complete(
    roles: &[BoundaryResidueRoleV1],
    selected_contexts: &BTreeSet<String>,
) -> bool {
    if roles.len() != selected_contexts.len() {
        return false;
    }
    if selected_contexts.iter().any(|context| {
        roles
            .iter()
            .filter(|role| role.context_ref == *context)
            .count()
            != 1
    }) {
        return false;
    }
    let role_set = roles
        .iter()
        .map(|role| role.role.as_str())
        .collect::<BTreeSet<_>>();
    ["core", "feature", "boundary"]
        .iter()
        .all(|role| role_set.contains(role))
}

fn boundary_residue_columns(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
    role_map: &BTreeMap<String, String>,
) -> Result<Vec<BoundaryResidueColumnV1>, String> {
    let mut columns = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "boundary-residue" && atom.predicate == "restrictionColumn")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        if !selected_contexts.contains(&atom.subject) {
            return Err(format!(
                "ag.boundary-residue restrictionColumn {} subject must be a selected source context",
                atom.normalized_atom_id
            ));
        }
        let source_role = role_map.get(&atom.subject).map(String::as_str);
        if !matches!(source_role, Some("core" | "feature")) {
            return Err(format!(
                "ag.boundary-residue restrictionColumn {} source context must be core or feature",
                atom.normalized_atom_id
            ));
        }
        let boundary_contexts = atom
            .context_memberships
            .iter()
            .filter(|context| role_map.get(*context).map(String::as_str) == Some("boundary"))
            .cloned()
            .collect::<Vec<_>>();
        if boundary_contexts.len() != 1 {
            return Err(format!(
                "ag.boundary-residue restrictionColumn {} must target exactly one boundary context",
                atom.normalized_atom_id
            ));
        }
        let support = boundary_residue_atom_support(atom, witness_variables)?;
        columns.push(BoundaryResidueColumnV1 {
            column_id: atom.normalized_atom_id.clone(),
            source_context: atom.subject.clone(),
            boundary_context: boundary_contexts[0].clone(),
            vector: boundary_residue_vector(&support, witness_variables),
            support,
            context_refs: atom.context_memberships.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    columns.sort_by(|left, right| left.column_id.cmp(&right.column_id));
    Ok(columns)
}

fn boundary_residue_mismatch(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
    role_map: &BTreeMap<String, String>,
) -> Result<Option<BoundaryResidueMismatchV1>, String> {
    let mut atom_refs = Vec::new();
    let mut context_refs = BTreeSet::new();
    let mut source_refs = BTreeSet::new();
    let mut vector = vec![0u8; witness_variables.len()];
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "boundary-residue" && atom.predicate == "boundarySection")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let selected_memberships = atom
            .context_memberships
            .iter()
            .filter(|context| selected_contexts.contains(*context))
            .collect::<Vec<_>>();
        if selected_memberships.is_empty()
            || selected_memberships
                .iter()
                .any(|context| role_map.get(*context).map(String::as_str) != Some("boundary"))
        {
            return Err(format!(
                "ag.boundary-residue boundarySection {} must belong only to selected boundary contexts",
                atom.normalized_atom_id
            ));
        }
        let support = boundary_residue_atom_support(atom, witness_variables)?;
        let atom_vector = boundary_residue_vector(&support, witness_variables);
        for (target, value) in vector.iter_mut().zip(atom_vector.iter()) {
            *target ^= *value;
        }
        atom_refs.push(atom.normalized_atom_id.clone());
        context_refs.extend(atom.context_memberships.iter().cloned());
        source_refs.extend(atom.source_refs.iter().cloned());
    }
    if atom_refs.is_empty() {
        return Ok(None);
    }
    let support = witness_variables
        .iter()
        .zip(vector.iter())
        .filter_map(|(variable, value)| (*value == 1).then_some(variable.clone()))
        .collect::<Vec<_>>();
    Ok(Some(BoundaryResidueMismatchV1 {
        atom_refs,
        support,
        vector,
        context_refs: context_refs.into_iter().collect(),
        source_refs: source_refs.into_iter().collect(),
    }))
}

fn boundary_residue_atom_support(
    atom: &NormalizedAtomV2,
    witness_variables: &[String],
) -> Result<Vec<String>, String> {
    let support = parse_csv_values(atom.object.as_deref().unwrap_or_default())
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let unknown = support
        .iter()
        .filter(|variable| !witness_set.contains(*variable))
        .cloned()
        .collect::<Vec<_>>();
    if !unknown.is_empty() {
        return Err(format!(
            "ag.boundary-residue atom {} contains variables outside law-surface witness variables: {}",
            atom.normalized_atom_id,
            unknown.join(",")
        ));
    }
    Ok(support)
}

fn boundary_residue_vector(support: &[String], witness_variables: &[String]) -> Vec<u8> {
    witness_variables
        .iter()
        .map(|variable| support.contains(variable) as u8)
        .collect()
}

fn boundary_residue_matrix_rows(
    columns: &[BoundaryResidueColumnV1],
    row_count: usize,
) -> Vec<Vec<u8>> {
    (0..row_count)
        .map(|row| columns.iter().map(|column| column.vector[row]).collect())
        .collect()
}

fn boundary_residue_invariant_json(
    profile: &MeasurementProfileV1,
    method_status: &str,
    witness_variables: &[String],
    roles: &[BoundaryResidueRoleV1],
    columns: &[BoundaryResidueColumnV1],
    mismatch: Option<&BoundaryResidueMismatchV1>,
    image_membership: Option<bool>,
) -> Value {
    let matrix_rows = boundary_residue_matrix_rows(columns, witness_variables.len());
    json!({
        "invariantId": format!("boundary-residue:{}", profile.profile_id),
        "evaluator": "ag.boundary-residue",
        "method": "finite-mayer-vietoris-d0@1",
        "claimScope": "selected-cover core/feature/boundary F2 Mayer-Vietoris boundary residue",
        "selectedCoverRef": profile.cover_ref,
        "coefficient": profile.coefficient,
        "methodStatus": method_status,
        "patchRoles": roles.iter().map(|role| json!({
            "atomRef": role.atom_ref,
            "contextRef": role.context_ref,
            "role": role.role,
            "sourceRefs": role.source_refs
        })).collect::<Vec<_>>(),
        "restrictionMatrix": {
            "rowBasis": witness_variables,
            "columnCount": columns.len(),
            "rank": matrix_rank_f2(matrix_rows),
            "columns": columns.iter().map(|column| json!({
                "columnId": column.column_id,
                "sourceContext": column.source_context,
                "boundaryContext": column.boundary_context,
                "support": column.support,
                "vector": column.vector,
                "contextRefs": column.context_refs,
                "sourceRefs": column.source_refs
            })).collect::<Vec<_>>()
        },
        "boundarySection": mismatch.map(|mismatch| json!({
            "atomRefs": mismatch.atom_refs,
            "support": mismatch.support,
            "vector": mismatch.vector,
            "contextRefs": mismatch.context_refs,
            "sourceRefs": mismatch.source_refs
        })),
        "imageMembership": image_membership,
        "boundaryNote": "Boundary residue is measured only as an F2 Mayer-Vietoris d0 image-membership reading over the selected finite cover; Z-zero lifting is assumed, and no pi1 or monodromy verdict is generated.",
        "nonConclusions": [
            "This evaluator does not generate a period-Stokes or modelRelative reading.",
            "This evaluator does not generate a pi1 or monodromy verdict.",
            "Z-zero holonomy lifting is recorded only as an assumption over the F2 parity reading."
        ]
    })
}

fn boundary_residue_assumptions(
    profile: &MeasurementProfileV1,
    method_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    let classification_checked = method_status != "boundary_classification_absent";
    let matrix_checked = matches!(
        method_status,
        "finite_mayer_vietoris_d0_computed" | "finite_mayer_vietoris_d0_obstruction_only"
    );
    let coefficient_checked = profile.coefficient == "F2";
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P1-2-classification".to_string(),
            assumption:
                "selected cover supplies core, feature, and boundary patch classification atoms"
                    .to_string(),
            status: if classification_checked {
                "checked"
            } else {
                "violated"
            }
            .to_string(),
            checked_by: classification_checked
                .then(|| format!("measurement-profile:{}.coverRef", profile.profile_id)),
            assumed_by: (!classification_checked)
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P1-2-d0".to_string(),
            assumption:
                "selected boundary mismatch section and finite core/feature restriction columns define Mayer-Vietoris d0 over F2"
                    .to_string(),
            status: if matrix_checked { "checked" } else { "violated" }.to_string(),
            checked_by: matrix_checked
                .then(|| "law-surface:provided-law-equation-surface".to_string()),
            assumed_by: (!matrix_checked).then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P1-2-coefficient".to_string(),
            assumption: "F2 parity coefficient reading is fixed or explicitly projected for boundary residue".to_string(),
            status: if coefficient_checked { "checked" } else { "assumed" }.to_string(),
            checked_by: coefficient_checked.then(|| {
                format!(
                    "measurement-profile:{}.coefficient=F2",
                    profile.profile_id
                )
            }),
            assumed_by: (!coefficient_checked)
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P1-2-z-zero".to_string(),
            assumption: "Z-zero holonomy lifting is assumed from the F2 parity reading only"
                .to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P1-2-pi1-boundary".to_string(),
            assumption:
                "boundary residue is a finite restriction-structure reading, not a pi1 or monodromy verdict"
                    .to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn square_free_generators_from_law_surface(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    law: &crate::LawEquationV1,
    witness_variables: &[String],
    archmap_aliases: &BTreeMap<String, String>,
    binding_axis: &str,
    binding_predicate: &str,
) -> Result<Vec<SquareFreeGeneratorV1>, String> {
    let (observed_axis, observed_predicate) =
        observation_selector("square-free", binding_axis, binding_predicate)?;
    let declared_supports = declared_law_supports(law, witness_variables)?;
    let support_atoms = normalized
        .atoms
        .iter()
        .filter(|atom| is_raw_support_predicate(atom))
        .filter(|atom| atom.axis == observed_axis && atom.predicate == observed_predicate)
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .collect::<Vec<_>>();
    let mut generators = Vec::new();
    for (index, support) in declared_supports.iter().enumerate() {
        let support_atom_refs = support_atoms
            .iter()
            .filter(|atom| {
                observed_support_matches(
                    atom,
                    support,
                    archmap_aliases,
                    observed_axis,
                    observed_predicate,
                )
            })
            .map(|atom| atom.normalized_atom_id.clone())
            .collect::<Vec<_>>();
        generators.push(SquareFreeGeneratorV1 {
            generator_id: format!("law-surface:{}:generator:{}", law.law_id, index + 1),
            support: support.clone(),
            support_atom_refs,
        });
    }
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
    _normalized: &NormalizedArchMapV2,
    _selected_contexts: &BTreeSet<String>,
    minimal_forbidden_supports: &[Vec<String>],
    repair_hitting_sets: &[Vec<String>],
    generators: &[SquareFreeGeneratorV1],
    witness_variable_count: usize,
    invariant_id: &str,
) -> Result<Option<SquareFreeCertificateV1>, String> {
    if minimal_forbidden_supports.is_empty() {
        return Ok(None);
    }
    let verification = compute_square_free_nsdepth_certificate(
        minimal_forbidden_supports,
        repair_hitting_sets,
        generators,
        witness_variable_count,
    );
    Ok(Some(SquareFreeCertificateV1 {
        cert_ref: format!("computedInvariants/{invariant_id}"),
        nsdepth: verification.nsdepth,
        support_atom_refs: verification.support_atom_refs,
        verified_minimal_forbidden_supports: verification.verified_minimal_forbidden_supports,
        status: verification.status,
        effect: verification.effect,
    }))
}

#[derive(Debug, Clone)]
struct SquareFreeCertificateVerificationV1 {
    nsdepth: Option<usize>,
    support_atom_refs: Vec<String>,
    verified_minimal_forbidden_supports: Vec<Vec<String>>,
    status: String,
    effect: String,
}

fn compute_square_free_nsdepth_certificate(
    minimal_forbidden_supports: &[Vec<String>],
    repair_hitting_sets: &[Vec<String>],
    generators: &[SquareFreeGeneratorV1],
    witness_variable_count: usize,
) -> SquareFreeCertificateVerificationV1 {
    let nsdepth = repair_hitting_sets.iter().map(Vec::len).max().unwrap_or(0);
    if nsdepth > witness_variable_count {
        return square_free_certificate_unverified(
            Some(nsdepth),
            "not_computed",
            "computed NSdepth exceeds selected witness family size; structural verdict follows observed support atom occurrence",
        );
    }
    let support_atom_refs = generators
        .iter()
        .flat_map(|generator| generator.support_atom_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    SquareFreeCertificateVerificationV1 {
        nsdepth: Some(nsdepth),
        support_atom_refs,
        verified_minimal_forbidden_supports: minimal_forbidden_supports.to_vec(),
        status: "computed".to_string(),
        effect:
            "ArchSig computed NSdepth from selected raw supports, minimal forbidden supports, and the finite Alexander-dual hitting-set depth rule; structural verdict follows observed support atom occurrence"
                .to_string(),
    }
}

fn is_raw_support_predicate(atom: &NormalizedAtomV2) -> bool {
    matches!(atom.predicate.as_str(), "support" | "cooccurrence")
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

fn delta_faces_from_forbidden_supports(
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

fn delta_link_faces(delta_faces: &[Vec<String>], vertex: &str) -> Vec<Vec<String>> {
    let face_set = delta_faces.iter().cloned().collect::<BTreeSet<_>>();
    let mut link_faces = delta_faces
        .iter()
        .filter(|face| !face.iter().any(|entry| entry == vertex))
        .filter_map(|face| {
            let mut with_vertex = face.clone();
            with_vertex.push(vertex.to_string());
            with_vertex.sort();
            face_set.contains(&with_vertex).then(|| face.clone())
        })
        .collect::<Vec<_>>();
    link_faces.sort();
    link_faces.dedup();
    link_faces
}

fn simplicial_boundary_rank_reading(faces: &[Vec<String>]) -> Vec<Value> {
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
    (1..=max_degree)
        .map(|degree| {
            json!({
                "domainDegree": degree,
                "codomainDegree": degree - 1,
                "rank": boundary_rank_f2(&simplices_by_degree, degree)
            })
        })
        .collect()
}

fn simplicial_component_count(faces: &[Vec<String>]) -> usize {
    let vertices = faces
        .iter()
        .filter(|face| face.len() == 1)
        .map(|face| face[0].clone())
        .collect::<BTreeSet<_>>();
    if vertices.is_empty() {
        return 0;
    }

    let mut adjacency = vertices
        .iter()
        .map(|vertex| (vertex.clone(), BTreeSet::<String>::new()))
        .collect::<BTreeMap<_, _>>();
    for edge in faces.iter().filter(|face| face.len() == 2) {
        if let [left, right] = edge.as_slice() {
            adjacency
                .entry(left.clone())
                .or_default()
                .insert(right.clone());
            adjacency
                .entry(right.clone())
                .or_default()
                .insert(left.clone());
        }
    }

    let mut seen = BTreeSet::<String>::new();
    let mut count = 0;
    for vertex in vertices {
        if !seen.insert(vertex.clone()) {
            continue;
        }
        count += 1;
        let mut stack = vec![vertex];
        while let Some(current) = stack.pop() {
            if let Some(neighbors) = adjacency.get(&current) {
                for neighbor in neighbors {
                    if seen.insert(neighbor.clone()) {
                        stack.push(neighbor.clone());
                    }
                }
            }
        }
    }
    count
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
    let section_value_atoms = normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "cech" && atom.predicate == "sectionValue")
        .collect::<Vec<_>>();
    let explicit_mismatch_atoms = normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "cech" && atom.predicate == "cocycleValue")
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
            let edge_id = format!("{}->{}", edge_key.2, edge_key.3);
            let reverse_edge_id = format!("{}->{}", edge_key.3, edge_key.2);
            let explicit_support = explicit_mismatch_atoms
                .iter()
                .filter(|atom| atom.subject == edge_id || atom.subject == reverse_edge_id)
                .collect::<Vec<_>>();
            let (value, support_atom_refs, observed) = if explicit_support.is_empty() {
                let source_values = cech_section_values(&section_value_atoms, &edge_key.2);
                let target_values = cech_section_values(&section_value_atoms, &edge_key.3);
                let observed = !source_values.is_empty() && !target_values.is_empty();
                let mismatch = observed && source_values != target_values;
                let support_atom_refs = if mismatch {
                    section_value_atoms
                        .iter()
                        .filter(|atom| atom.subject == edge_key.2 || atom.subject == edge_key.3)
                        .map(|atom| atom.normalized_atom_id.clone())
                        .collect::<Vec<_>>()
                } else {
                    Vec::new()
                };
                (u8::from(mismatch), support_atom_refs, observed)
            } else {
                let value = explicit_support.iter().any(|atom| {
                    atom.object
                        .as_deref()
                        .is_some_and(|object| matches!(object.trim(), "1" | "true" | "nonzero"))
                });
                let support_atom_refs = if value {
                    explicit_support
                        .iter()
                        .map(|atom| atom.normalized_atom_id.clone())
                        .collect::<Vec<_>>()
                } else {
                    Vec::new()
                };
                (u8::from(value), support_atom_refs, true)
            };
            edges.push(CechEdgeV1 {
                edge_id,
                source_context: edge_key.2,
                target_context: edge_key.3,
                value,
                support_atom_refs,
                observed,
            });
        }
    }
    edges.sort_by(|left, right| left.edge_id.cmp(&right.edge_id));
    edges
}

fn cech_section_values(atoms: &[&NormalizedAtomV2], context_id: &str) -> BTreeSet<String> {
    atoms
        .iter()
        .filter(|atom| atom.subject == context_id)
        .filter_map(|atom| atom.object.as_deref())
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(str::to_string)
        .collect()
}

fn coherence_faces(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    cover_ref: &str,
) -> Vec<CoherenceFaceV1> {
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let mut edge_by_pair = BTreeMap::new();
    for edge in edges {
        edge_by_pair.insert(
            sorted_pair(&edge.source_context, &edge.target_context),
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
                let contexts = vec![
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
                    edge_by_pair.get(&sorted_pair(&contexts[0], &contexts[1])),
                    edge_by_pair.get(&sorted_pair(&contexts[0], &contexts[2])),
                    edge_by_pair.get(&sorted_pair(&contexts[1], &contexts[2])),
                ]
                .into_iter()
                .flatten()
                .cloned()
                .collect::<Vec<_>>();
                faces.push(CoherenceFaceV1 {
                    face_id: format!(
                        "coherence-face:{}:{}:{}:{}",
                        cover_ref, contexts[0], contexts[1], contexts[2]
                    ),
                    context_refs: contexts,
                    edge_refs,
                    shared_atom_refs,
                });
            }
        }
    }
    faces.sort_by(|left, right| left.face_id.cmp(&right.face_id));
    faces
}

fn coherence_tetrahedra(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &[String],
    faces: &[CoherenceFaceV1],
) -> Vec<CoherenceTetrahedronV1> {
    let face_by_contexts = faces
        .iter()
        .map(|face| {
            (
                face.context_refs.iter().cloned().collect::<BTreeSet<_>>(),
                face.face_id.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
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
    let mut tetrahedra = Vec::new();
    for first in 0..selected_contexts.len() {
        for second in first + 1..selected_contexts.len() {
            for third in second + 1..selected_contexts.len() {
                for fourth in third + 1..selected_contexts.len() {
                    let contexts = vec![
                        selected_contexts[first].clone(),
                        selected_contexts[second].clone(),
                        selected_contexts[third].clone(),
                        selected_contexts[fourth].clone(),
                    ];
                    let Some(shared_atom_refs) =
                        shared_atoms_for_contexts(&atom_refs_by_context, &contexts)
                    else {
                        continue;
                    };
                    if shared_atom_refs.is_empty() {
                        continue;
                    }
                    let mut face_refs = Vec::new();
                    for omitted in 0..contexts.len() {
                        let face_contexts = contexts
                            .iter()
                            .enumerate()
                            .filter(|(index, _)| *index != omitted)
                            .map(|(_, context)| context.clone())
                            .collect::<BTreeSet<_>>();
                        let Some(face_ref) = face_by_contexts.get(&face_contexts) else {
                            face_refs.clear();
                            break;
                        };
                        face_refs.push(face_ref.clone());
                    }
                    if face_refs.len() != 4 {
                        continue;
                    }
                    tetrahedra.push(CoherenceTetrahedronV1 {
                        tetrahedron_id: format!(
                            "coherence-tetrahedron:{}:{}:{}:{}",
                            contexts[0], contexts[1], contexts[2], contexts[3]
                        ),
                        context_refs: contexts,
                        face_refs,
                        shared_atom_refs,
                    });
                }
            }
        }
    }
    tetrahedra.sort_by(|left, right| left.tetrahedron_id.cmp(&right.tetrahedron_id));
    tetrahedra
}

fn shared_atoms_for_contexts(
    atom_refs_by_context: &BTreeMap<String, BTreeSet<String>>,
    contexts: &[String],
) -> Option<Vec<String>> {
    let mut iter = contexts.iter();
    let first = iter.next()?;
    let mut shared = atom_refs_by_context.get(first)?.clone();
    for context in iter {
        let atoms = atom_refs_by_context.get(context)?;
        shared = shared.intersection(atoms).cloned().collect();
    }
    Some(shared.into_iter().collect())
}

fn coherence_witness_atoms<'a>(
    normalized: &'a NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
) -> Vec<&'a NormalizedAtomV2> {
    normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "coherence")
        .filter(|atom| {
            matches!(
                atom.predicate.as_str(),
                "tripleSection" | "coherenceSection" | "h2Section"
            )
        })
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .collect()
}

fn coherence_witnesses_for_faces(
    witness_atoms: &[&NormalizedAtomV2],
    faces: &[CoherenceFaceV1],
) -> Vec<CoherenceWitnessV1> {
    let mut witnesses = Vec::new();
    for atom in witness_atoms {
        for face in faces {
            if coherence_atom_marks_face(atom, face) {
                witnesses.push(CoherenceWitnessV1 {
                    atom_ref: atom.normalized_atom_id.clone(),
                    face_ref: face.face_id.clone(),
                    context_refs: face.context_refs.clone(),
                    source_refs: atom.source_refs.clone(),
                });
            }
        }
    }
    witnesses.sort_by(|left, right| {
        left.face_ref
            .cmp(&right.face_ref)
            .then_with(|| left.atom_ref.cmp(&right.atom_ref))
    });
    witnesses
}

fn coherence_atom_marks_face(atom: &NormalizedAtomV2, face: &CoherenceFaceV1) -> bool {
    let mut refs = atom.source_refs.iter().cloned().collect::<BTreeSet<_>>();
    refs.extend(atom.context_memberships.iter().cloned());
    refs.insert(atom.subject.clone());
    if let Some(object) = atom.object.as_deref() {
        refs.extend(parse_csv_values(object));
    }
    refs.contains(&face.face_id)
        || face.context_refs.iter().all(|context| {
            refs.contains(context)
                || refs.contains(unprefixed(context))
                || refs.contains(&format!("ctx:{}", unprefixed(context)))
        })
}

fn coherence_d1_rows(edges: &[CechEdgeV1], faces: &[CoherenceFaceV1]) -> Vec<Vec<u8>> {
    let edge_index = edges
        .iter()
        .enumerate()
        .map(|(index, edge)| (edge.edge_id.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut rows = vec![vec![0u8; edges.len()]; faces.len()];
    for (row, face) in faces.iter().enumerate() {
        for edge_ref in &face.edge_refs {
            if let Some(column) = edge_index.get(edge_ref) {
                rows[row][*column] ^= 1;
            }
        }
    }
    rows
}

fn coherence_d2_rows(
    faces: &[CoherenceFaceV1],
    tetrahedra: &[CoherenceTetrahedronV1],
) -> Vec<Vec<u8>> {
    let face_index = faces
        .iter()
        .enumerate()
        .map(|(index, face)| (face.face_id.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut rows = vec![vec![0u8; faces.len()]; tetrahedra.len()];
    for (row, tetrahedron) in tetrahedra.iter().enumerate() {
        for face_ref in &tetrahedron.face_refs {
            if let Some(column) = face_index.get(face_ref) {
                rows[row][*column] ^= 1;
            }
        }
    }
    rows
}

fn vector_in_span_f2(rows: &[Vec<u8>], vector: &[u8]) -> bool {
    if rows.len() != vector.len() {
        return false;
    }
    if vector.iter().all(|value| *value == 0) {
        return true;
    }
    let rank = matrix_rank_f2(rows.to_vec());
    let mut augmented = rows.to_vec();
    for (row, value) in augmented.iter_mut().zip(vector.iter()) {
        row.push(*value);
    }
    matrix_rank_f2(augmented) == rank
}

fn h2_representative_f2(
    d2_rows: &[Vec<u8>],
    d1_rows: &[Vec<u8>],
    face_count: usize,
) -> Option<Vec<u8>> {
    nullspace_basis_f2(d2_rows, face_count)
        .into_iter()
        .find(|candidate| !vector_in_span_f2(d1_rows, candidate))
}

fn nullspace_basis_f2(rows: &[Vec<u8>], columns: usize) -> Vec<Vec<u8>> {
    let mut rref = rows
        .iter()
        .map(|row| {
            let mut normalized = vec![0u8; columns];
            for (column, value) in row.iter().take(columns).enumerate() {
                normalized[column] = value & 1;
            }
            normalized
        })
        .collect::<Vec<_>>();
    let mut pivot_columns = Vec::new();
    let mut pivot_row = 0usize;

    for column in 0..columns {
        let Some(row) = (pivot_row..rref.len()).find(|row| rref[*row][column] == 1) else {
            continue;
        };
        rref.swap(pivot_row, row);
        for row in 0..rref.len() {
            if row != pivot_row && rref[row][column] == 1 {
                for entry in column..columns {
                    rref[row][entry] ^= rref[pivot_row][entry];
                }
            }
        }
        pivot_columns.push(column);
        pivot_row += 1;
        if pivot_row == rref.len() {
            break;
        }
    }

    let pivot_set = pivot_columns.iter().copied().collect::<BTreeSet<_>>();
    (0..columns)
        .filter(|column| !pivot_set.contains(column))
        .map(|free_column| {
            let mut vector = vec![0u8; columns];
            vector[free_column] = 1;
            for (row, pivot_column) in pivot_columns.iter().enumerate() {
                if rref[row][free_column] == 1 {
                    vector[*pivot_column] = 1;
                }
            }
            vector
        })
        .collect()
}

fn coherence_representative_json(cochain: &[u8], faces: &[CoherenceFaceV1]) -> Vec<Value> {
    faces
        .iter()
        .zip(cochain.iter())
        .filter(|(_, value)| **value == 1)
        .map(|(face, _)| {
            json!({
                "faceRef": face.face_id,
                "contextRefs": face.context_refs,
                "sharedAtomRefs": face.shared_atom_refs
            })
        })
        .collect::<Vec<_>>()
}

fn sorted_pair(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_string(), right.to_string())
    } else {
        (right.to_string(), left.to_string())
    }
}

#[allow(clippy::too_many_arguments)]
fn coherence_invariant_json(
    profile: &MeasurementProfileV1,
    status: &str,
    method_status: &str,
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    faces: &[CoherenceFaceV1],
    tetrahedra: &[CoherenceTetrahedronV1],
    witnesses: &[CoherenceWitnessV1],
    cochain: &[u8],
    rank_d1: usize,
    rank_ker_d2: usize,
    h2_dimension: usize,
    d2_row_count: usize,
    cocycle_gate_passed: bool,
    representative: Vec<Value>,
) -> Value {
    json!({
        "invariantId": format!("coherence-obstruction:{}", profile.profile_id),
        "evaluator": "ag.coherence-obstruction",
        "method": "finite-f2-h2-coherence@1",
        "status": status,
        "methodStatus": method_status,
        "claimScope": "selected-cover banded abelian F2 H2 coherence calculation",
        "selectedCoverRef": profile.cover_ref,
        "coefficient": profile.coefficient,
        "cohomologyQuotient": "ker d^2/im d^1",
        "contextCount": selected_contexts.len(),
        "edgeCount": edges.len(),
        "faceCount": faces.len(),
        "tetrahedronCount": tetrahedra.len(),
        "rankD1": rank_d1,
        "rankKerD2": rank_ker_d2,
        "h2Dimension": h2_dimension,
        "d2RowCount": d2_row_count,
        "cocycleGate": {
            "condition": "d2 h = 0",
            "passed": cocycle_gate_passed
        },
        "faces": faces.iter().enumerate().map(|(index, face)| json!({
            "faceId": face.face_id,
            "contextRefs": face.context_refs,
            "edgeRefs": face.edge_refs,
            "sharedAtomRefs": face.shared_atom_refs,
            "cochainValue": cochain.get(index).copied()
        })).collect::<Vec<_>>(),
        "tetrahedra": tetrahedra.iter().map(|tetrahedron| json!({
            "tetrahedronId": tetrahedron.tetrahedron_id,
            "contextRefs": tetrahedron.context_refs,
            "faceRefs": tetrahedron.face_refs,
            "sharedAtomRefs": tetrahedron.shared_atom_refs
        })).collect::<Vec<_>>(),
        "coherenceWitnesses": witnesses.iter().map(|witness| json!({
            "atomRef": witness.atom_ref,
            "faceRef": witness.face_ref,
            "contextRefs": witness.context_refs,
            "sourceRefs": witness.source_refs
        })).collect::<Vec<_>>(),
        "representative": representative,
        "nonConclusions": [
            "This is cover-relative H2 over banded abelian F2, not a non-abelian gerbe verdict.",
            "H1 Cech verdict rows are not changed by this evaluator."
        ]
    })
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
                "sectionObservation": if edge.observed { "observed" } else { "not_observed" },
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
        "faceSource": "selected cover triple-overlap sharedAtomRefs recorded in archsig-measurement-packet/v0.5.4; not inferred by the viewer",
        "h2CoherenceVisualized": false
    })
}

fn project_h2_coherence_to_cover_nerve(
    mut cover_nerve_projection: Value,
    packet: &ArchSigMeasurementPacketV1,
) -> Value {
    let Some(coherence_row) = packet
        .structural_verdict
        .iter()
        .find(|row| row.evaluator == "ag.coherence-obstruction")
    else {
        return cover_nerve_projection;
    };
    if coherence_row.verdict != "measured_zero" && coherence_row.verdict != "measured_nonzero" {
        return cover_nerve_projection;
    }
    let Some(coherence_invariant) = packet
        .computed_invariants
        .iter()
        .find(|invariant| invariant["evaluator"] == "ag.coherence-obstruction")
    else {
        return cover_nerve_projection;
    };

    let structural_ref = structural_verdict_ref(coherence_row);
    let representative_contexts = coherence_invariant["representative"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(context_key)
        .collect::<BTreeSet<_>>();
    let measured_faces = coherence_invariant["faces"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|face| {
            let key = context_key(face)?;
            let cochain_value = face["cochainValue"].as_u64().unwrap_or_default();
            Some((key, cochain_value))
        })
        .collect::<BTreeMap<_, _>>();

    let mut visualized = false;
    if let Some(faces) = cover_nerve_projection["faces"].as_array_mut() {
        for face in faces {
            let Some(key) = context_key(face) else {
                continue;
            };
            if !measured_faces.contains_key(&key) {
                continue;
            }
            let claim = if coherence_row.verdict == "measured_nonzero"
                && representative_contexts.contains(&key)
            {
                "measured_nonzero"
            } else {
                "measured_zero"
            };
            if let Some(object) = face.as_object_mut() {
                object.insert(
                    "coherenceClaim".to_string(),
                    Value::String(claim.to_string()),
                );
                object.insert("h2CoherenceVisualized".to_string(), Value::Bool(true));
                object.insert(
                    "structuralVerdictRef".to_string(),
                    Value::String(structural_ref.clone()),
                );
                object.insert(
                    "coherenceProjectionBoundary".to_string(),
                    Value::String(
                        "Projected from ag.coherence-obstruction; viewer adds no H2 verdict"
                            .to_string(),
                    ),
                );
            }
            visualized = true;
        }
    }
    if visualized {
        cover_nerve_projection["h2CoherenceVisualized"] = Value::Bool(true);
    }
    cover_nerve_projection
}

fn context_key(value: &Value) -> Option<String> {
    let mut contexts = value["contextRefs"]
        .as_array()?
        .iter()
        .filter_map(Value::as_str)
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    if contexts.is_empty() {
        return None;
    }
    contexts.sort();
    Some(contexts.join("|"))
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

pub fn build_measurement_viewer_data_v1(
    normalized: &NormalizedArchMapV2,
    archmap_document: &ArchMapDocumentV2,
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
    let atom_nodes = viewer_atom_nodes(&viewer_atoms, archmap_document, insight_report);
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
    let saga_descent = build_saga_descent_viewer_projection(packet);
    json!({
        "schema": "archsig-atom-viewer-data/v0.5.4",
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
        "sagaDescent": saga_descent,
        "aatGeometryOverlays": {
            "schema": "archsig-aat-geometry-overlays/v0.5.4",
            "projectionBoundary": "bounded viewer projection of measured ArchSig AG geometry; visual richness is not a new verdict",
            "gluingGeometry": insight_report["gluingGeometry"],
            "nerve": insight_report["gluingGeometry"]["nerve"],
            "cocycleRibbon": insight_report["gluingGeometry"]["cocycleRibbon"],
            "locusField": insight_report["gluingGeometry"]["locusField"],
            "spectrumLandscape": insight_report["gluingGeometry"]["spectrumLandscape"],
            "forbiddenCages": insight_report["gluingGeometry"]["forbiddenCages"],
            "repairMorphs": insight_report["gluingGeometry"]["repairMorphs"],
            "atomGlyphs": insight_report["gluingGeometry"]["atomGlyphs"],
            "analyticOverlayBundle": insight_report["gluingGeometry"]["analyticOverlayBundle"],
            "periodStokes": insight_report["gluingGeometry"]["periodStokes"],
            "periodPairingOverlays": insight_report["gluingGeometry"]["analyticOverlayBundle"]["periodPairingOverlays"],
            "transferCostOverlays": insight_report["gluingGeometry"]["analyticOverlayBundle"]["transferCostOverlays"],
            "spectralGapOverlays": insight_report["gluingGeometry"]["analyticOverlayBundle"]["spectralGapOverlays"],
            "curvatureHotspotOverlays": insight_report["gluingGeometry"]["analyticOverlayBundle"]["curvatureHotspotOverlays"],
            "singularityConcentrationOverlays": insight_report["gluingGeometry"]["analyticOverlayBundle"]["singularityConcentrationOverlays"],
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

fn build_saga_descent_viewer_projection(packet: &ArchSigMeasurementPacketV1) -> Value {
    let mut field_map = Vec::new();
    let mut grounding_rows = Vec::new();
    let mut descent_rows = Vec::new();

    for (index, row) in packet.structural_verdict.iter().enumerate() {
        let stage = match row.evaluator.as_str() {
            "ag.saga-grounded" => "grounding",
            "ag.saga-descent" => "descent",
            _ => continue,
        };
        let mut row_value = json!({
            "evaluator": row.evaluator,
            "law": row.law,
            "verdict": row.verdict,
            "inScope": row.verdict_data.in_scope,
            "zero": row.verdict_data.zero,
            "nonZero": row.verdict_data.non_zero,
            "methodStatus": row.verdict_data.method_status,
            "reason": row.reason,
            "dependsOnAssumptions": row.depends_on_assumptions
        });
        if let Some(cert_ref) = row.verdict_data.cert_ref.as_ref() {
            row_value["certRef"] = json!(cert_ref);
        }
        let row_index = if stage == "grounding" {
            grounding_rows.len()
        } else {
            descent_rows.len()
        };
        let prefix = if stage == "grounding" {
            format!("stages[0].rows[{row_index}]")
        } else {
            format!("stages[1].rows[{row_index}]")
        };
        for field in [
            "evaluator",
            "law",
            "verdict",
            "inScope",
            "zero",
            "nonZero",
            "methodStatus",
            "certRef",
            "reason",
            "dependsOnAssumptions",
        ] {
            let packet_path = if field == "inScope"
                || field == "zero"
                || field == "nonZero"
                || field == "methodStatus"
                || field == "certRef"
            {
                format!("/structuralVerdict/{index}/verdictData/{field}")
            } else {
                format!("/structuralVerdict/{index}/{field}")
            };
            if let Some(value) = row_value.get(field) {
                append_leaf_field_mappings(
                    &mut field_map,
                    &format!("{prefix}.{field}"),
                    &packet_path,
                    value,
                );
            }
        }
        if stage == "grounding" {
            grounding_rows.push(row_value);
        } else {
            descent_rows.push(row_value);
        }
    }

    let mut measurement_rows = Vec::new();
    let mut comparison_rows = Vec::new();
    let mut harmonic_rows = Vec::new();
    for (index, invariant) in packet.computed_invariants.iter().enumerate() {
        let Some(invariant_id) = invariant["invariantId"].as_str() else {
            continue;
        };
        if invariant_id == "saga-generated-end-to-end-packet"
            && invariant["evaluator"].as_str() == Some("ag.saga-grounded")
        {
            let row_index = grounding_rows.len();
            let mut row = serde_json::Map::new();
            for (output_field, source_path) in [
                ("invariantId", "invariantId"),
                ("evaluator", "evaluator"),
                ("theoremRef", "theoremRef"),
                ("premise", "lawDependent.premise"),
                ("detectorFindings", "detectorFindings"),
                ("detectorCount", "detectorCount"),
            ] {
                let value = if source_path == "lawDependent.premise" {
                    invariant["lawDependent"]["premise"].clone()
                } else {
                    invariant[source_path].clone()
                };
                if !value.is_null() {
                    row.insert(output_field.to_string(), value);
                    let packet_path = if source_path == "lawDependent.premise" {
                        format!("/computedInvariants/{index}/lawDependent/premise")
                    } else {
                        format!("/computedInvariants/{index}/{source_path}")
                    };
                    append_leaf_field_mappings(
                        &mut field_map,
                        &format!("stages[0].rows[{row_index}].{output_field}"),
                        &packet_path,
                        &row[output_field],
                    );
                }
            }
            grounding_rows.push(Value::Object(row));
        } else if invariant["evaluator"].as_str() == Some("ag.saga-descent")
            && (invariant_id == "saga-descent:residual-class"
                || invariant_id == "saga-descent:boundary-membership"
                || invariant_id == "saga-descent:closure-diagnostics")
        {
            let measurement_index = measurement_rows.len();
            let mut row = serde_json::Map::new();
            row.insert("invariantId".to_string(), json!(invariant_id));
            for field in ["invariantId", "evaluator", "status", "reason", "whatNext"] {
                if let Some(value) = invariant.get(field) {
                    row.insert(field.to_string(), value.clone());
                    append_leaf_field_mappings(
                        &mut field_map,
                        &format!("stages[1].measurements[{measurement_index}].{field}"),
                        &format!("/computedInvariants/{index}/{field}"),
                        value,
                    );
                }
            }
            for (output_field, source_path) in [
                ("residualClass", "residualClassSupport"),
                ("boundaryMembership", "boundaryMembership"),
                ("closureDiagnostics", "closureDiagnostics"),
                ("faithfulnessBasis", "faithfulnessBasis"),
            ] {
                if let Some(value) = invariant.get(source_path) {
                    row.insert(output_field.to_string(), value.clone());
                    append_leaf_field_mappings(
                        &mut field_map,
                        &format!("stages[1].measurements[{measurement_index}].{output_field}"),
                        &format!("/computedInvariants/{index}/{source_path}"),
                        value,
                    );
                }
            }
            measurement_rows.push(Value::Object(row));
        } else if invariant_id == "saga-comparison:h1-transfer"
            && invariant["evaluator"].as_str() == Some("ag.saga-comparison")
        {
            let comparison_index = comparison_rows.len();
            let mut row = serde_json::Map::new();
            for field in [
                "invariantId",
                "evaluator",
                "kind",
                "status",
                "reason",
                "whatNext",
                "conclusionCode",
                "failureCode",
                "contract",
            ] {
                if let Some(value) = invariant.get(field) {
                    row.insert(field.to_string(), value.clone());
                    append_leaf_field_mappings(
                        &mut field_map,
                        &format!("stages[2].rows[{comparison_index}].{field}"),
                        &format!("/computedInvariants/{index}/{field}"),
                        value,
                    );
                }
            }
            comparison_rows.push(Value::Object(row));
        } else if invariant["evaluator"] == "ag.harmonic-debt" {
            let harmonic_index = harmonic_rows.len();
            let mut row = serde_json::Map::new();
            for field in [
                "invariantId",
                "evaluator",
                "status",
                "reason",
                "whatNext",
                "essentialRepairLowerBound",
                "lowerBoundStatus",
            ] {
                if let Some(value) = invariant.get(field) {
                    row.insert(field.to_string(), value.clone());
                    append_leaf_field_mappings(
                        &mut field_map,
                        &format!("stages[1].harmonicDebt[{harmonic_index}].{field}"),
                        &format!("/computedInvariants/{index}/{field}"),
                        value,
                    );
                }
            }
            harmonic_rows.push(Value::Object(row));
        }
    }

    for (index, reading) in packet.analytic_readings.iter().enumerate() {
        if reading.evaluator != "ag.harmonic-debt" {
            continue;
        }
        let harmonic_index = harmonic_rows.len();
        let mut row = serde_json::Map::new();
        row.insert("readingId".to_string(), json!(reading.reading_id));
        row.insert("evaluator".to_string(), json!(reading.evaluator));
        if let Some(regime) = reading.regime.as_ref() {
            row.insert("regime".to_string(), json!(regime));
        }
        row.insert("value".to_string(), reading.value.clone());
        for (field, value) in &row {
            append_leaf_field_mappings(
                &mut field_map,
                &format!("stages[1].harmonicDebt[{harmonic_index}].{field}"),
                &format!("/analyticReadings/{index}/{field}"),
                value,
            );
        }
        harmonic_rows.push(Value::Object(row));
    }

    let mut silence_rows = packet
        .boundary_statements
        .iter()
        .enumerate()
        .filter(|(_, statement)| {
            statement.kind == "silence_by_design"
                && statement
                    .scope_refs
                    .iter()
                    .any(|scope_ref| saga_scope_ref(packet, scope_ref))
        })
        .enumerate()
        .map(|(row_index, (packet_index, statement))| {
            let row = json!({
                "id": statement.id,
                "status": statement.kind,
                "reason": statement.reason,
                "whatNext": statement.text,
                "scopeRefs": statement.scope_refs
            });
            for (field, packet_field) in [
                ("id", "id"),
                ("status", "kind"),
                ("reason", "reason"),
                ("whatNext", "text"),
                ("scopeRefs", "scopeRefs"),
            ] {
                let value = &row[field];
                let packet_path = format!("/boundaryStatements/{packet_index}/{packet_field}");
                append_leaf_field_mappings(
                    &mut field_map,
                    &format!("silenceRows[{row_index}].{field}"),
                    &packet_path,
                    value,
                );
                append_leaf_field_mappings(
                    &mut field_map,
                    &format!("stages[3].rows[{row_index}].{field}"),
                    &packet_path,
                    value,
                );
            }
            row
        })
        .collect::<Vec<_>>();

    for (index, invariant) in packet.computed_invariants.iter().enumerate() {
        if invariant["status"] != "silence_by_design"
            || !matches!(
                invariant["evaluator"].as_str(),
                Some("ag.saga-grounded")
                    | Some("ag.saga-descent")
                    | Some("ag.saga-comparison")
                    | Some("ag.harmonic-debt")
            )
        {
            continue;
        }
        let row_index = silence_rows.len();
        let mut row = json!({
            "id": invariant["invariantId"],
            "status": "silence_by_design",
        });
        for field in ["reason", "whatNext"] {
            if let Some(value) = invariant.get(field).filter(|value| !value.is_null()) {
                row[field] = value.clone();
            }
        }
        for (field, packet_field) in [
            ("id", "invariantId"),
            ("status", "status"),
            ("reason", "reason"),
            ("whatNext", "whatNext"),
        ] {
            if let Some(value) = row.get(field).filter(|value| !value.is_null()) {
                let packet_path = format!("/computedInvariants/{index}/{packet_field}");
                append_leaf_field_mappings(
                    &mut field_map,
                    &format!("silenceRows[{row_index}].{field}"),
                    &packet_path,
                    value,
                );
                append_leaf_field_mappings(
                    &mut field_map,
                    &format!("stages[3].rows[{row_index}].{field}"),
                    &packet_path,
                    value,
                );
            }
        }
        silence_rows.push(row);
    }

    let grounding_status = projected_stage_status(&[&grounding_rows]);
    let descent_status =
        projected_stage_status(&[&descent_rows, &measurement_rows, &harmonic_rows]);
    let comparison_status = projected_stage_status(&[&comparison_rows]);

    json!({
        "projectionBoundary": "Every displayed measurement value is selected from the measurement packet or its SAGA-scoped boundary statements; stage status is a presentation aggregation of displayed packet rows and no viewer verdict is synthesized.",
        "sourcePacketRef": "archsig-measurement-packet.json",
        "stages": [
            {
                "stageId": "grounding",
                "order": 0,
                "status": grounding_status,
                "rows": grounding_rows,
                "measurements": [],
                "visualRole": "grounding"
            },
            {
                "stageId": "descent",
                "order": 1,
                "status": descent_status,
                "rows": descent_rows,
                "measurements": measurement_rows,
                "harmonicDebt": harmonic_rows,
                "visualRole": "descent-measurement"
            },
            {
                "stageId": "comparison",
                "order": 2,
                "status": comparison_status,
                "rows": comparison_rows,
                "visualRole": "transfer-comparison"
            },
            {
                "stageId": "silence",
                "order": 3,
                "status": if silence_rows.is_empty() { "not_computed" } else { "silence_by_design" },
                "rows": silence_rows.clone(),
                "visualRole": "silence"
            }
        ],
        "silenceRows": silence_rows,
        "leafFieldMap": field_map,
        "nonClaims": [
            "The projection does not create structural verdicts, comparison results, or repair decisions.",
            "A missing packet field remains absent; silence_by_design remains visible as a silence row."
        ]
    })
}

fn projected_stage_status(groups: &[&[Value]]) -> &'static str {
    let values = groups
        .iter()
        .flat_map(|group| group.iter())
        .collect::<Vec<_>>();
    if values.is_empty() {
        return "not_computed";
    }
    let statuses = values
        .iter()
        .filter_map(|value| {
            value["status"]
                .as_str()
                .or_else(|| value["verdict"].as_str())
        })
        .collect::<Vec<_>>();
    if statuses.is_empty() {
        return "measured";
    }
    if statuses.iter().all(|status| *status == "silence_by_design") {
        return "silence_by_design";
    }
    if statuses
        .iter()
        .all(|status| *status == "not_computed" || *status == "silence_by_design")
    {
        return "not_computed";
    }
    if statuses.iter().any(|status| {
        matches!(
            *status,
            "measured_nonzero" | "obstruction" | "blocked" | "residual_not_in_b1"
        )
    }) {
        return "measured_nonzero";
    }
    if statuses.iter().all(|status| {
        matches!(
            *status,
            "measured_zero" | "zero" | "established" | "complete_support_global_coherent"
        )
    }) {
        return "measured_zero";
    }
    "measured"
}

fn saga_scope_ref(packet: &ArchSigMeasurementPacketV1, scope_ref: &str) -> bool {
    if scope_ref.starts_with("structuralVerdict/") {
        return packet.structural_verdict.iter().any(|row| {
            structural_verdict_ref(row) == scope_ref && is_saga_evaluator(&row.evaluator)
        });
    }
    if let Some(index) = scope_ref
        .strip_prefix("computedInvariants/")
        .and_then(|index| index.parse::<usize>().ok())
    {
        return packet
            .computed_invariants
            .get(index)
            .is_some_and(|row| row["evaluator"].as_str().is_some_and(is_saga_evaluator));
    }
    packet.computed_invariants.iter().any(|row| {
        row["invariantId"] == scope_ref && row["evaluator"].as_str().is_some_and(is_saga_evaluator)
    }) || packet
        .analytic_readings
        .iter()
        .any(|reading| reading.reading_id == scope_ref && is_saga_evaluator(&reading.evaluator))
}

fn is_saga_evaluator(evaluator: &str) -> bool {
    matches!(
        evaluator,
        "ag.saga-grounded" | "ag.saga-descent" | "ag.saga-comparison" | "ag.harmonic-debt"
    )
}

fn append_leaf_field_mappings(
    field_map: &mut Vec<Value>,
    viewer_path: &str,
    packet_path: &str,
    value: &Value,
) {
    match value {
        Value::Object(object) => {
            for (key, child) in object {
                append_leaf_field_mappings(
                    field_map,
                    &format!("{viewer_path}.{key}"),
                    &format!("{packet_path}/{key}"),
                    child,
                );
            }
        }
        Value::Array(array) => {
            for (index, child) in array.iter().enumerate() {
                append_leaf_field_mappings(
                    field_map,
                    &format!("{viewer_path}[{index}]"),
                    &format!("{packet_path}/{index}"),
                    child,
                );
            }
        }
        _ => field_map.push(json!({
            "viewerPath": viewer_path,
            "packetPath": packet_path
        })),
    }
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

/// Resolves a semantic source ref (an `archmap.sources` key) into the file
/// path / symbol / line evidence declared by the supplied ArchMap, following
/// one `source` indirection for symbol entries. Unresolvable refs keep the
/// bare `ref` form; the viewer must not invent locations.
fn resolved_source_ref_sample(archmap_document: &ArchMapDocumentV2, reference: &str) -> Value {
    let mut sample = json!({ "ref": reference });
    let mut cited_line = None;
    let entry = match archmap_document.sources.get(reference) {
        Some(entry) => entry,
        None => {
            let Some((base, line)) = crate::archmap::source_ref_line_base(reference) else {
                return sample;
            };
            let Some(entry) = archmap_document.sources.get(base) else {
                return sample;
            };
            cited_line = Some(line);
            entry
        }
    };
    sample["sourceKind"] = json!(entry.kind);
    let path = entry.path.clone().or_else(|| {
        entry
            .source
            .as_ref()
            .and_then(|parent| archmap_document.sources.get(parent))
            .and_then(|parent| parent.path.clone())
    });
    if let Some(path) = path {
        sample["path"] = json!(path);
    }
    if let Some(symbol) = &entry.symbol {
        sample["symbol"] = json!(symbol);
    }
    if let Some(line) = entry.line {
        sample["line"] = json!(line);
    }
    // A cited `:line` suffix is more specific than the source entry's own line.
    if let Some(line) = cited_line {
        sample["line"] = json!(line);
    }
    if let Some(section) = &entry.section {
        sample["section"] = json!(section);
    }
    sample
}

fn viewer_atom_nodes(
    atoms: &[NormalizedAtomV2],
    archmap_document: &ArchMapDocumentV2,
    insight_report: &Value,
) -> Vec<Value> {
    let top_atoms = top_insight_atom_refs(insight_report);
    atoms
        .iter()
        .map(|atom| {
            let source_refs = atom
                .source_refs
                .iter()
                .map(|source_ref| resolved_source_ref_sample(archmap_document, source_ref))
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

#[cfg(test)]
fn validate_measurement_packet_v1(packet: &ArchSigMeasurementPacketV1) -> Vec<ValidationCheck> {
    let packet_value = serde_json::to_value(packet).unwrap_or_else(|_| json!({}));
    validate_measurement_packet_components(packet, &packet_value)
}

pub fn validate_measurement_packet_value_v1(packet_value: &Value) -> Vec<ValidationCheck> {
    let typed_packet =
        match serde_json::from_value::<ArchSigMeasurementPacketV1>(packet_value.clone()) {
            Ok(packet) => packet,
            Err(error) => {
                let mut check = validation_check(
                    "measurement-packet-schema052-typed-shape",
                    "measurement packet parses as ArchSigMeasurementPacketV1",
                    "fail",
                );
                check.reason = Some(format!("measurement packet shape is invalid: {error}"));
                return vec![check];
            }
        };
    validate_measurement_packet_components(&typed_packet, packet_value)
}

fn validate_measurement_packet_components(
    packet: &ArchSigMeasurementPacketV1,
    packet_value: &Value,
) -> Vec<ValidationCheck> {
    vec![
        check_packet_unknown_fields(packet_value),
        check_packet_schema(packet),
        check_structural_verdict_values(packet),
        check_structural_verdict_evaluators(packet),
        check_structural_verdict_data(packet),
        check_structural_verdict_new_shape_value(packet_value),
        check_computed_invariant_shape_value(packet_value),
        check_saga_presentation_generated_evidence_value(packet_value),
        check_analytic_regime_boundary(packet, packet_value),
        check_assumption_ledger_value(packet, packet_value),
        check_supplied_data_shape(packet),
        check_boundary_statements(packet),
    ]
}

fn check_packet_unknown_fields(packet_value: &Value) -> ValidationCheck {
    let mut examples = Vec::new();
    check_object_keys(
        packet_value,
        "measurementPacket",
        &[
            "schema",
            "packetId",
            "profile",
            "profiles",
            "structuralVerdict",
            "computedInvariants",
            "analyticReadings",
            "assumptions",
            "suppliedData",
            "boundaryStatements",
            "nonConclusions",
            "toolVersion",
            "runId",
            "inputDigests",
            "componentFingerprints",
        ],
        &mut examples,
    );
    check_object_keys(
        &packet_value["profile"],
        "profile",
        &[
            "schema",
            "profileId",
            "siteRef",
            "coverRef",
            "coefficient",
            "effCoeff",
            "resolutionSelector",
            "domain",
            "zeroPredicate",
            "nonZeroPredicate",
            "certSelector",
            "verdictDiscipline",
            "diagnosticCeiling",
            "analytic",
            "finiteBounds",
        ],
        &mut examples,
    );
    check_object_keys(
        &packet_value["profile"]["finiteBounds"],
        "profile.finiteBounds",
        &[
            "maxSquareFreeWitnessVariables",
            "maxCoherenceContexts",
            "maxTorWitnessVariables",
            "maxBoundaryResidueVariables",
            "maxLaplacianCells",
            "maxPeriodCycles",
            "maxTransferTargets",
        ],
        &mut examples,
    );
    // This is the union of the normalized schema fields and the evaluator-specific
    // fields emitted by the current measurement packet producers.
    const COMPUTED_INVARIANT_FIELDS: &[&str] = &[
        "invariantId",
        "id",
        "readingId",
        "computedInvariantId",
        "kind",
        "evaluator",
        "value",
        "representation",
        "archmapRef",
        "atomCount",
        "contextCount",
        "coverCount",
        "doctrineFingerprint",
        "boundaryNote",
        "claimScope",
        "conclusionCode",
        "contract",
        "classSupport",
        "coefficient",
        "coverNerveProjection",
        "dimensions",
        "method",
        "methodStatus",
        "nerveShape",
        "observedCocycle",
        "rankD0",
        "reason",
        "restrictionEdgeCount",
        "selectedCoverRef",
        "selectedH2",
        "status",
        "whatNext",
        "theorem12_4Discharge",
        "b1NerveReading",
        "capacityFormula",
        "capacityLowerBound",
        "eulerCharacteristic",
        "eulerFormula",
        "measuredCechVerdictEcho",
        "structuralVerdictRef",
        "selectedSectionRef",
        "sectionFactorization",
        "restrictionCompatibility",
        "boundaryMembership",
        "minimalForbiddenSupports",
        "alexanderDualRepair",
        "transferTargets",
        "residue",
        "pairings",
        "periods",
        "laplacian",
        "cochainCells",
        "sagaConclusionCode",
        "diagnosticCeiling",
        "residualKind",
        "commonAmbient",
        "lawConflicts",
        "lawIdeals",
        "nonConclusions",
        "proxyComparison",
        "resolution",
        "resolutionSelectorEffective",
        "torByDegree",
        "witnessVariables",
        "analyticReadingRef",
        "assumptionBoundary",
        "boundarySection",
        "cellRefs",
        "closureDiagnostics",
        "cocycleGate",
        "coherenceWitnesses",
        "cohomologyQuotient",
        "components",
        "cycleBasis",
        "d2RowCount",
        "deltaComplex",
        "dimension",
        "edgeChecks",
        "edgeCount",
        "faceCount",
        "faces",
        "facetDimensionReading",
        "facets",
        "faithfulnessBasis",
        "failureCode",
        "forms",
        "h2Dimension",
        "imageMembership",
        "irreducibleComponentCount",
        "isPure",
        "laplacianMatrix",
        "linkBoundaryReading",
        "linkReducedBetti",
        "locusSymbol",
        "nsdepthCertificate",
        "obstructionIdeal",
        "pairingAtomRefs",
        "patchRoles",
        "periodPairingMatrix",
        "rankD1",
        "rankKerD2",
        "repairPathAtomRefs",
        "repairPlanRef",
        "representative",
        "residualClassSupport",
        "suppliedSlots",
        "suppliedCochainMap",
        "presentationGenerated",
        "generatedQuotientTransfer",
        "resolutionSelector",
        "restrictionMatrix",
        "sectionAssignment",
        "sourceRefs",
        "stokesAudit",
        "supportLocalizedPremise",
        "tetrahedra",
        "tetrahedronCount",
        "transferMeasurementPairing",
        "transferResidue",
        "violatedForbiddenSupports",
        "wassersteinTransferCost",
        "schema",
        "groundedSurfaceRef",
        "theoremRef",
        "lawDependent",
        "lawIndependent",
        "degreeZeroLawContribution",
        "generatedQuotient",
        "detectorFindings",
        "detectorCount",
        "observedEdgeCount",
        "unobservedEdgeRefs",
        "sectionObservation",
        "harmonicDebtNorm",
        "essentialRepairLowerBound",
        "lowerBoundStatus",
        "sourceProxyReading",
        "nonConclusion",
    ];
    for (index, invariant) in packet_value["computedInvariants"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        check_object_keys(
            invariant,
            &format!("computedInvariants[{index}]"),
            COMPUTED_INVARIANT_FIELDS,
            &mut examples,
        );
        let is_comparison_kind = invariant["kind"].as_str() == Some("h1-comparison-transfer");
        let is_comparison_evaluator = invariant["evaluator"].as_str() == Some("ag.saga-comparison");
        if is_comparison_kind || is_comparison_evaluator {
            let contract_label = format!("computedInvariants[{index}].contract");
            if is_comparison_kind && !is_comparison_evaluator {
                examples.push(generic_validation_example(
                    &format!("computedInvariants[{index}]"),
                    "evaluator",
                    "h1-comparison-transfer kind is owned by ag.saga-comparison",
                ));
            }
            if is_comparison_evaluator && !is_comparison_kind {
                examples.push(generic_validation_example(
                    &format!("computedInvariants[{index}]"),
                    "kind",
                    "ag.saga-comparison evaluator is owned by h1-comparison-transfer kind",
                ));
            }
            if is_comparison_kind && !is_comparison_evaluator && invariant.get("contract").is_some()
            {
                examples.push(generic_validation_example(
                    &contract_label,
                    "contract",
                    "contract is reserved for ag.saga-comparison owned computed invariants",
                ));
            }
            let Some(contract) = invariant.get("contract") else {
                examples.push(generic_validation_example(
                    &contract_label,
                    "contract",
                    "ag.saga-comparison computed invariants must carry contract",
                ));
                continue;
            };
            if !contract.is_object() {
                examples.push(generic_validation_example(
                    &contract_label,
                    "contract",
                    "ag.saga-comparison contract must be an object",
                ));
            } else {
                check_object_keys(
                    contract,
                    &contract_label,
                    &[
                        "incidenceBridgeKind",
                        "h1ComparisonDataKind",
                        "normalizedComplexFingerprint",
                        "classPrerequisite",
                        "targetClassComputed",
                        "contractChecked",
                    ],
                    &mut examples,
                );
                for (field, valid) in [
                    (
                        "incidenceBridgeKind",
                        contract["incidenceBridgeKind"].is_string(),
                    ),
                    (
                        "h1ComparisonDataKind",
                        contract["h1ComparisonDataKind"].is_string(),
                    ),
                    (
                        "normalizedComplexFingerprint",
                        contract["normalizedComplexFingerprint"].is_string(),
                    ),
                    (
                        "classPrerequisite",
                        contract["classPrerequisite"].is_boolean(),
                    ),
                    (
                        "targetClassComputed",
                        contract["targetClassComputed"].is_boolean(),
                    ),
                    ("contractChecked", contract["contractChecked"].is_boolean()),
                ] {
                    if !valid {
                        examples.push(generic_validation_example(
                            &contract_label,
                            field,
                            "comparison contract field has the wrong type or is missing",
                        ));
                    }
                }
                let status = invariant["status"].as_str();
                let class_prerequisite = contract["classPrerequisite"].as_bool();
                let target_class_computed = contract["targetClassComputed"].as_bool();
                let contract_checked = contract["contractChecked"].as_bool();
                let failure_code = invariant["failureCode"].as_str();
                let conclusion_code = invariant["conclusionCode"].as_str();
                let established_conclusion = if contract["h1ComparisonDataKind"].as_str()
                    == Some("presentation-generated")
                {
                    ARCHSIG_SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS
                } else {
                    ARCHSIG_SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA
                };
                if failure_code
                    .is_some_and(|code| code != ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION)
                {
                    examples.push(generic_validation_example(
                        &contract_label,
                        "failureCode",
                        "comparison failureCode must be COMPARISON_DATA_CONTRACT_VIOLATION",
                    ));
                }
                if status == Some("silence_by_design") {
                    if class_prerequisite != Some(false) {
                        examples.push(generic_validation_example(
                            &contract_label,
                            "classPrerequisite",
                            "silence_by_design comparison requires classPrerequisite=false",
                        ));
                    }
                    if failure_code.is_some() || conclusion_code.is_some() {
                        examples.push(generic_validation_example(
                            &contract_label,
                            "status",
                            "silence_by_design comparison cannot carry failureCode or conclusionCode",
                        ));
                    }
                }
                if status == Some("established") {
                    if class_prerequisite != Some(true)
                        || target_class_computed != Some(true)
                        || contract_checked != Some(true)
                    {
                        examples.push(generic_validation_example(
                            &contract_label,
                            "status",
                            "established comparison requires all contract completion flags=true",
                        ));
                    }
                    if conclusion_code != Some(established_conclusion) || failure_code.is_some()
                    {
                        examples.push(generic_validation_example(
                            &contract_label,
                            "conclusionCode",
                            "established comparison requires its conclusionCode and no failureCode",
                        ));
                    }
                }
                if status == Some("not_computed") {
                    if matches!(
                        conclusion_code,
                        Some(ARCHSIG_SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA)
                            | Some(ARCHSIG_SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS)
                    )
                    {
                        examples.push(generic_validation_example(
                            &contract_label,
                            "conclusionCode",
                            "not_computed comparison cannot carry the established conclusionCode",
                        ));
                    }
                    let measured_source_and_target =
                        class_prerequisite == Some(true) && target_class_computed == Some(true);
                    if measured_source_and_target
                        && failure_code != Some(ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION)
                    {
                        examples.push(generic_validation_example(
                            &contract_label,
                            "failureCode",
                            "not_computed comparison with measured source and target classes requires COMPARISON_DATA_CONTRACT_VIOLATION",
                        ));
                    }
                }
            }
        } else if invariant.get("contract").is_some() {
            let contract_label = format!("computedInvariants[{index}].contract");
            examples.push(generic_validation_example(
                &contract_label,
                "contract",
                "contract is reserved for ag.saga-comparison computed invariants",
            ));
        }
    }
    for (index, row) in packet_value["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let prefix = format!("structuralVerdict[{index}]");
        check_object_keys(
            row,
            &prefix,
            &[
                "verdictRef",
                "evaluator",
                "law",
                "target",
                "verdict",
                "verdictData",
                "dependsOnAssumptions",
                "evidence",
                "reason",
            ],
            &mut examples,
        );
        check_object_keys(
            &row["target"],
            &format!("{prefix}.target"),
            &["kind", "coverRef", "coefficient", "scopeSize", "classRef"],
            &mut examples,
        );
        check_object_keys(
            &row["target"]["scopeSize"],
            &format!("{prefix}.target.scopeSize"),
            &["contexts", "edges", "triangles"],
            &mut examples,
        );
        check_object_keys(
            &row["verdictData"],
            &format!("{prefix}.verdictData"),
            &["inScope", "zero", "nonZero", "methodStatus", "certRef"],
            &mut examples,
        );
        check_object_keys(
            &row["evidence"],
            &format!("{prefix}.evidence"),
            &["computedInvariantRefs", "sourceRefs"],
            &mut examples,
        );
    }
    for (index, reading) in packet_value["analyticReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        check_object_keys(
            reading,
            &format!("analyticReadings[{index}]"),
            &[
                "readingId",
                "evaluator",
                "claimStatus",
                "fidelity",
                "value",
                "regime",
                "structuralVerdictRef",
            ],
            &mut examples,
        );
    }
    for (index, assumption) in packet_value["assumptions"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        check_object_keys(
            assumption,
            &format!("assumptions[{index}]"),
            &[
                "assumptionId",
                "theoremRef",
                "assumption",
                "status",
                "checkedBy",
                "assumedBy",
                "scopeRefs",
            ],
            &mut examples,
        );
    }
    for (index, supplied) in packet_value["suppliedData"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        check_object_keys(
            supplied,
            &format!("suppliedData[{index}]"),
            &["suppliedId", "kind", "sourceArtifactRef", "conformance"],
            &mut examples,
        );
        check_object_keys(
            &supplied["conformance"],
            &format!("suppliedData[{index}].conformance"),
            &["status", "checkRef", "boundary"],
            &mut examples,
        );
    }
    for (index, boundary) in packet_value["boundaryStatements"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        check_object_keys(
            boundary,
            &format!("boundaryStatements[{index}]"),
            &["id", "kind", "scopeRefs", "reason", "text"],
            &mut examples,
        );
    }
    check_examples(
        "measurement-packet-schema052-unknown-fields",
        "measurement packet objects reject unknown fields",
        examples,
    )
}

fn check_object_keys(
    value: &Value,
    path: &str,
    allowed: &[&str],
    examples: &mut Vec<ValidationExample>,
) {
    let Some(object) = value.as_object() else {
        return;
    };
    for key in object.keys() {
        if !allowed.contains(&key.as_str()) {
            examples.push(generic_validation_example(
                &format!("{path}.{key}"),
                "unknown",
                "unknown measurement packet fields are rejected",
            ));
        }
    }
}

fn check_required_object_keys(
    value: &Value,
    path: &str,
    required: &[&str],
    examples: &mut Vec<ValidationExample>,
) -> bool {
    let Some(object) = value.as_object() else {
        examples.push(generic_validation_example(
            path,
            "object",
            "generated SAGA evidence must be an object with its documented fields",
        ));
        return false;
    };
    check_object_keys(value, path, required, examples);
    for field in required {
        if !object.contains_key(*field) {
            examples.push(generic_validation_example(
                &format!("{path}.{field}"),
                "required",
                "generated SAGA evidence field is required",
            ));
        }
    }
    true
}

fn check_packet_schema(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let mut check = validation_check(
        "measurement-packet-schema052-schema",
        "measurement packet uses archsig-measurement-packet/v0.5.4",
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
        "measurement-packet-schema052-five-verdict-values",
        "structural verdicts are limited to the five v0.5.4 values",
        examples,
    )
}

fn check_structural_verdict_evaluators(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let examples = packet
        .structural_verdict
        .iter()
        .filter(|row| !STRUCTURAL_VERDICT_EVALUATORS.contains(&row.evaluator.as_str()))
        .map(|row| {
            generic_validation_example(
                &row.evaluator,
                &row.law,
                "structural verdict evaluators must stay within the registered AG measurement surface",
            )
        })
        .collect::<Vec<_>>();
    check_examples(
        "measurement-packet-schema052-structural-verdict-evaluators",
        "structural verdict rows are limited to registered AG measurement evaluators",
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
        if row.verdict == "measured_zero" && row.verdict_data.non_zero {
            examples.push(generic_validation_example(
                &row.evaluator,
                "measured_zero",
                "measured_zero requires nonZero=false in VerdictData",
            ));
        }
        if row.verdict == "measured_zero" && !row.verdict_data.in_scope {
            examples.push(generic_validation_example(
                &row.evaluator,
                "measured_zero",
                "measured_zero requires inScope=true in VerdictData",
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
        "measurement-packet-schema052-verdict-data-boundary",
        "VerdictData keeps zero, nonzero, unmeasured, unknown, and not_computed separate",
        examples,
    )
}

fn check_structural_verdict_new_shape_value(packet_value: &Value) -> ValidationCheck {
    let invariant_ids = packet_value["computedInvariants"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|invariant| invariant["invariantId"].as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    let mut verdict_refs = BTreeSet::new();
    for (index, row) in packet_value["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let row_label = format!("structuralVerdict[{index}]");
        if let Some(verdict_ref) = row["verdictRef"].as_str() {
            if !verdict_refs.insert(verdict_ref) {
                examples.push(generic_validation_example(
                    &row_label,
                    verdict_ref,
                    "structural verdict verdictRef values must be unique",
                ));
            }
        }
        if row["verdictRef"].as_str().is_none_or(str::is_empty) {
            examples.push(generic_validation_example(
                &row_label,
                "verdictRef",
                "structural verdict rows must carry a non-empty verdictRef",
            ));
        } else {
            let expected_verdict_ref = format!(
                "structuralVerdict/{}/{}/{}",
                measurement_ref_segment(row["evaluator"].as_str().unwrap_or_default()),
                measurement_ref_segment(row["law"].as_str().unwrap_or_default()),
                measurement_ref_segment(
                    row["verdictData"]["methodStatus"]
                        .as_str()
                        .or_else(|| row["methodStatus"].as_str())
                        .unwrap_or_default(),
                )
            );
            if row["verdictRef"].as_str() != Some(expected_verdict_ref.as_str()) {
                examples.push(generic_validation_example(
                    &row_label,
                    "verdictRef",
                    "verdictRef must be derived from evaluator, law, and methodStatus",
                ));
            }
        }
        let target = &row["target"];
        if !target.is_object() {
            examples.push(generic_validation_example(
                &row_label,
                "target",
                "structural verdict rows must carry target block",
            ));
            continue;
        }
        for field in ["kind", "coverRef", "coefficient"] {
            if target[field].as_str().is_none_or(str::is_empty) {
                examples.push(generic_validation_example(
                    &row_label,
                    field,
                    "target kind / coverRef / coefficient must be non-empty",
                ));
            }
        }
        if target["coverRef"].as_str() != packet_value["profile"]["coverRef"].as_str() {
            examples.push(generic_validation_example(
                &row_label,
                "target.coverRef",
                "structural verdict target.coverRef must equal profile.coverRef",
            ));
        }
        if target["coefficient"].as_str() != packet_value["profile"]["coefficient"].as_str() {
            examples.push(generic_validation_example(
                &row_label,
                "target.coefficient",
                "structural verdict target.coefficient must equal profile.coefficient",
            ));
        }
        if !target["scopeSize"].is_object() {
            examples.push(generic_validation_example(
                &row_label,
                "target.scopeSize",
                "target.scopeSize must be an object",
            ));
        }
        let Some(evidence) = row.get("evidence").and_then(Value::as_object) else {
            examples.push(generic_validation_example(
                &row_label,
                "evidence",
                "structural verdict rows must carry evidence block",
            ));
            continue;
        };
        let Some(computed_refs_value) = evidence.get("computedInvariantRefs") else {
            examples.push(generic_validation_example(
                &row_label,
                "evidence.computedInvariantRefs",
                "structural verdict evidence must carry computedInvariantRefs array",
            ));
            continue;
        };
        let Some(computed_refs_array) = computed_refs_value.as_array() else {
            examples.push(generic_validation_example(
                &row_label,
                "evidence.computedInvariantRefs",
                "structural verdict evidence computedInvariantRefs must be an array",
            ));
            continue;
        };
        let mut computed_refs = Vec::new();
        for (ref_index, invariant_ref) in computed_refs_array.iter().enumerate() {
            let Some(invariant_ref) = invariant_ref.as_str().filter(|value| !value.is_empty())
            else {
                examples.push(generic_validation_example(
                    &row_label,
                    &format!("evidence.computedInvariantRefs[{ref_index}]"),
                    "computed invariant refs must be non-empty strings",
                ));
                continue;
            };
            computed_refs.push(invariant_ref);
        }
        match evidence.get("sourceRefs").and_then(Value::as_array) {
            None => examples.push(generic_validation_example(
                &row_label,
                "evidence.sourceRefs",
                "structural verdict evidence must carry sourceRefs array",
            )),
            Some(source_refs) => {
                for (ref_index, source_ref) in source_refs.iter().enumerate() {
                    if source_ref.as_str().is_none_or(str::is_empty) {
                        examples.push(generic_validation_example(
                            &row_label,
                            &format!("evidence.sourceRefs[{ref_index}]"),
                            "source refs must be non-empty strings",
                        ));
                    }
                }
            }
        }
        if matches!(
            row["verdict"].as_str(),
            Some("measured_zero" | "measured_nonzero")
        ) && computed_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &row_label,
                "evidence.computedInvariantRefs",
                "measured verdicts must name supporting computed invariants",
            ));
        }
        for invariant_ref in computed_refs {
            if !invariant_ids.contains(invariant_ref) {
                examples.push(generic_validation_example(
                    &row_label,
                    invariant_ref,
                    "evidence.computedInvariantRefs must resolve to computedInvariants[].invariantId",
                ));
            } else if let Some(invariant_evaluator) = packet_value["computedInvariants"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|invariant| invariant["invariantId"].as_str() == Some(invariant_ref))
                .and_then(|invariant| invariant["evaluator"].as_str())
            {
                let row_evaluator = row["evaluator"].as_str().unwrap_or_default();
                if invariant_evaluator != row_evaluator {
                    examples.push(generic_validation_example(
                        &row_label,
                        invariant_ref,
                        &format!(
                            "computed invariant evaluator {invariant_evaluator} must match structural verdict evaluator {row_evaluator}"
                        ),
                        ));
                }
            } else {
                examples.push(generic_validation_example(
                    &row_label,
                    invariant_ref,
                    "referenced computed invariant must carry evaluator provenance",
                ));
            }
        }
        if row["verdict"].as_str() == Some("measured_zero")
            && !scope_size_has_positive_component(&target["scopeSize"])
        {
            examples.push(generic_validation_example(
                &row_label,
                "target.scopeSize",
                "measured_zero requires a non-vacuous positive target scopeSize",
            ));
        }
        if row["verdict"].as_str() == Some("measured_nonzero") {
            let Some(class_ref) = target["classRef"]
                .as_str()
                .filter(|value| !value.is_empty())
            else {
                examples.push(generic_validation_example(
                    &row_label,
                    "target.classRef",
                    "measured_nonzero requires target.classRef",
                ));
                continue;
            };
            if !invariant_ids.contains(class_ref)
                && !class_ref
                    .strip_prefix("computedInvariants/")
                    .is_some_and(|id| invariant_ids.contains(id))
            {
                examples.push(generic_validation_example(
                    &row_label,
                    class_ref,
                    "measured_nonzero target.classRef must resolve to computed invariant evidence",
                ));
            }
            let class_id = class_ref
                .strip_prefix("computedInvariants/")
                .unwrap_or(class_ref);
            if let Some(invariant_evaluator) = packet_value["computedInvariants"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|invariant| invariant["invariantId"].as_str() == Some(class_id))
                .and_then(|invariant| invariant["evaluator"].as_str())
            {
                let row_evaluator = row["evaluator"].as_str().unwrap_or_default();
                if invariant_evaluator != row_evaluator {
                    examples.push(generic_validation_example(
                        &row_label,
                        class_ref,
                        &format!(
                            "target.classRef evaluator {invariant_evaluator} must match structural verdict evaluator {row_evaluator}"
                        ),
                        ));
                }
            } else {
                examples.push(generic_validation_example(
                    &row_label,
                    class_ref,
                    "measured_nonzero classRef invariant must carry evaluator provenance",
                ));
            }
        }
    }
    check_examples(
        "measurement-packet-schema052-structural-verdict-new-shape",
        "structural verdict rows carry target and computed invariant evidence",
        examples,
    )
}

fn scope_size_has_positive_component(scope_size: &Value) -> bool {
    scope_size
        .as_object()
        .into_iter()
        .flat_map(|object| object.values())
        .any(|value| value.as_u64().is_some_and(|count| count > 0))
}

fn measurement_ref_segment(value: &str) -> String {
    value
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '-' })
        .collect()
}

fn check_computed_invariant_shape_value(packet_value: &Value) -> ValidationCheck {
    let mut examples = Vec::new();
    let mut invariant_ids = BTreeSet::new();
    for (index, invariant) in packet_value["computedInvariants"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let label = format!("computedInvariants[{index}]");
        if let Some(invariant_id) = invariant["invariantId"].as_str() {
            if !invariant_ids.insert(invariant_id) {
                examples.push(generic_validation_example(
                    &label,
                    invariant_id,
                    "computed invariant invariantId values must be unique",
                ));
            }
        }
        for field in ["invariantId", "kind"] {
            if invariant[field].as_str().is_none_or(str::is_empty) {
                examples.push(generic_validation_example(
                    &label,
                    field,
                    "computed invariant must carry invariantId and closed kind",
                ));
            }
        }
        if invariant["evaluator"].as_str().is_none_or(str::is_empty) {
            examples.push(generic_validation_example(
                &label,
                "evaluator",
                "computed invariant must carry evaluator provenance",
            ));
        }
        if let Some(kind) = invariant["kind"].as_str() {
            if !COMPUTED_INVARIANT_KINDS.contains(&kind) {
                examples.push(generic_validation_example(
                    &label,
                    kind,
                    "computed invariant kind must be one of the closed measurement packet v0.5.4 kinds",
                ));
            }
            if let Some((_, owner)) = COMPUTED_INVARIANT_KIND_OWNERS
                .iter()
                .find(|(owned_kind, _)| *owned_kind == kind)
                && invariant["evaluator"].as_str() != Some(owner)
            {
                examples.push(generic_validation_example(
                    &label,
                    "evaluator",
                    &format!("computed invariant kind {kind} must be owned by {owner}"),
                ));
            }
        }
        if invariant["evaluator"].as_str() == Some("ag.saga-grounded")
            && invariant["kind"].as_str() == Some("saga-grounded-conclusions")
            && invariant["status"].as_str() != Some("not_computed")
        {
            validate_saga_grounded_packet_shape(invariant, &label, &mut examples);
        }
        if invariant.get("value").is_none() || invariant.get("representation").is_none() {
            examples.push(generic_validation_example(
                &label,
                "value/representation",
                "computed invariant must carry typed value and representation",
            ));
        }
        if invariant["evaluator"].as_str() == Some("ag.square-free-repair")
            && invariant.get("obstructionIdeal").is_some()
        {
            let obstruction_label = format!("{label}.obstructionIdeal");
            check_object_keys(
                &invariant["obstructionIdeal"],
                &obstruction_label,
                &["id", "generators"],
                &mut examples,
            );
            let Some(generators) = invariant["obstructionIdeal"]["generators"].as_array() else {
                examples.push(generic_validation_example(
                    &obstruction_label,
                    "generators",
                    "square-free obstructionIdeal.generators must be an array",
                ));
                continue;
            };
            for (generator_index, generator) in generators.iter().enumerate() {
                let generator_label = format!("{obstruction_label}.generators[{generator_index}]");
                check_object_keys(
                    generator,
                    &generator_label,
                    &["generatorId", "support", "supportAtomRefs"],
                    &mut examples,
                );
                for field in ["generatorId", "support", "supportAtomRefs"] {
                    if field == "generatorId" {
                        if generator[field].as_str().is_none_or(str::is_empty) {
                            examples.push(generic_validation_example(
                                &generator_label,
                                field,
                                "square-free generators must carry a generatorId",
                            ));
                        }
                    } else if generator[field]
                        .as_array()
                        .is_none_or(|items| items.iter().any(|item| item.as_str().is_none()))
                    {
                        examples.push(generic_validation_example(
                            &generator_label,
                            field,
                            "square-free generator support fields must be arrays of strings",
                        ));
                    }
                }
            }
            if let Some(certificate) = invariant.get("nsdepthCertificate") {
                if !certificate.is_null() {
                    let certificate_label = format!("{label}.nsdepthCertificate");
                    check_object_keys(
                        certificate,
                        &certificate_label,
                        &[
                            "status",
                            "certificateRef",
                            "nsdepth",
                            "supportAtomRefs",
                            "verifiedMinimalForbiddenSupports",
                            "effect",
                        ],
                        &mut examples,
                    );
                    if certificate["status"].as_str() != Some("missing")
                        && certificate["supportAtomRefs"]
                            .as_array()
                            .is_none_or(|items| items.iter().any(|item| item.as_str().is_none()))
                    {
                        examples.push(generic_validation_example(
                            &certificate_label,
                            "supportAtomRefs",
                            "square-free NSdepth certificate supportAtomRefs must be an array of strings",
                        ));
                    }
                    if certificate["status"].as_str() == Some("computed")
                        && certificate["certificateRef"]
                            .as_str()
                            .is_none_or(|reference| !reference.starts_with("computedInvariants/"))
                    {
                        examples.push(generic_validation_example(
                            &certificate_label,
                            "certificateRef",
                            "computed square-free NSdepth certificates must reference their computed invariant",
                        ));
                    }
                }
            }
        }
    }
    check_examples(
        "measurement-packet-schema052-computed-invariants-typed",
        "computed invariants expose invariantId, kind, value, and representation",
        examples,
    )
}

fn check_saga_presentation_generated_evidence_value(packet_value: &Value) -> ValidationCheck {
    let mut examples = Vec::new();
    for (index, invariant) in packet_value["computedInvariants"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        if invariant["kind"].as_str() != Some("h1-comparison-transfer")
            || invariant["evaluator"].as_str() != Some("ag.saga-comparison")
            || invariant["contract"]["h1ComparisonDataKind"].as_str()
                != Some("presentation-generated")
        {
            continue;
        }
        let prefix = format!("computedInvariants[{index}]");
        let status = invariant["status"].as_str();
        let requires_generated_evidence =
            matches!(status, Some("established") | Some("not_computed"));
        let presentation = invariant.get("presentationGenerated");
        let parsed_presentation = match presentation {
            Some(value) if !value.is_null() => {
                check_saga_presentation_generated_evidence_shape(
                    value,
                    &format!("{prefix}.presentationGenerated"),
                    &mut examples,
                );
                match serde_json::from_value::<SagaPresentationGeneratedEvidenceV1>(value.clone()) {
                    Ok(evidence) => Some(evidence),
                    Err(error) => {
                        examples.push(generic_validation_example(
                            &format!("{prefix}.presentationGenerated"),
                            "typed-shape",
                            &format!(
                                "presentation-generated evidence must have the documented typed shape: {error}"
                            ),
                        ));
                        None
                    }
                }
            }
            _ if requires_generated_evidence => {
                examples.push(generic_validation_example(
                    &format!("{prefix}.presentationGenerated"),
                    "required",
                    "presentation-generated established or not_computed comparison requires generated evidence",
                ));
                None
            }
            _ => None,
        };

        if status == Some("established") {
            let Some(presentation) = parsed_presentation.as_ref() else {
                continue;
            };
            check_saga_presentation_generated_established_consistency(
                invariant,
                &prefix,
                presentation,
                &mut examples,
            );
        } else if invariant
            .get("generatedQuotientTransfer")
            .is_some_and(|value| !value.is_null())
        {
            examples.push(generic_validation_example(
                &format!("{prefix}.generatedQuotientTransfer"),
                "status",
                "presentation-generated quotient transfer is emitted only for established comparisons",
            ));
        }
    }
    check_examples(
        "measurement-packet-schema052-saga-presentation-generated-evidence",
        "presentation-generated SAGA evidence is typed, complete, and consistent with its transfer",
        examples,
    )
}

fn check_saga_presentation_generated_evidence_shape(
    value: &Value,
    path: &str,
    examples: &mut Vec<ValidationExample>,
) {
    let fields = [
        "kind",
        "presentationExactness",
        "generatorCompleteness",
        "generatedCochainMap",
        "equationResidual",
        "semanticResidual",
        "residualWitness",
        "restrictionNaturality",
    ];
    if !check_required_object_keys(value, path, &fields, examples) {
        return;
    }
    check_required_object_keys(
        &value["generatedCochainMap"],
        &format!("{path}.generatedCochainMap"),
        &[
            "kind",
            "degreeZero",
            "degreeOne",
            "degreeTwo",
            "degreeZeroCommutative",
            "degreeOneCommutative",
        ],
        examples,
    );
    check_required_object_keys(
        &value["equationResidual"],
        &format!("{path}.equationResidual"),
        &["kind", "targetCocycle", "targetClassNonZero"],
        examples,
    );
    check_required_object_keys(
        &value["semanticResidual"],
        &format!("{path}.semanticResidual"),
        &["kind", "sourceCocycle", "sourceClassNonZero"],
        examples,
    );
    for degree in ["degreeZero", "degreeOne", "degreeTwo"] {
        let rows = &value["generatedCochainMap"][degree];
        let Some(rows) = rows.as_array() else {
            examples.push(generic_validation_example(
                &format!("{path}.generatedCochainMap.{degree}"),
                "array",
                "generated cochain-map cell evidence must be an array",
            ));
            continue;
        };
        for (index, row) in rows.iter().enumerate() {
            check_required_object_keys(
                row,
                &format!("{path}.generatedCochainMap.{degree}[{index}]"),
                &["cellRef", "localPhiDerivedFrom"],
                examples,
            );
        }
    }
    let witness = &value["residualWitness"];
    if witness.is_null() {
        return;
    }
    if !check_required_object_keys(
        witness,
        &format!("{path}.residualWitness"),
        &[
            "kind",
            "equation",
            "sourceImage",
            "equationResidual",
            "h",
            "differenceIsDeltaZero",
        ],
        examples,
    ) {
        return;
    }
    for (field, reference) in [
        ("sourceImage", "overlapRef"),
        ("equationResidual", "overlapRef"),
        ("h", "chartRef"),
    ] {
        let rows = &witness[field];
        let Some(rows) = rows.as_array() else {
            examples.push(generic_validation_example(
                &format!("{path}.residualWitness.{field}"),
                "array",
                "computed quotient-atlas witness rows must be an array",
            ));
            continue;
        };
        for (index, row) in rows.iter().enumerate() {
            check_required_object_keys(
                row,
                &format!("{path}.residualWitness.{field}[{index}]"),
                &[reference, "equationGenerators", "coefficients"],
                examples,
            );
        }
    }
}

fn check_saga_presentation_generated_established_consistency(
    invariant: &Value,
    prefix: &str,
    presentation: &SagaPresentationGeneratedEvidenceV1,
    examples: &mut Vec<ValidationExample>,
) {
    if presentation.kind != "presentation-generated"
        || !presentation.presentation_exactness
        || !presentation.generator_completeness
        || !presentation.restriction_naturality
        || presentation.generated_cochain_map.kind != "derived-from-local-phi"
        || !presentation.generated_cochain_map.degree_zero_commutative
        || !presentation.generated_cochain_map.degree_one_commutative
        || presentation.equation_residual.kind != "derived-from-independent-equation-lift-atlas"
        || !presentation.equation_residual.target_cocycle
        || presentation.semantic_residual.kind != "derived-from-semantic-repair-presentation"
        || !presentation.semantic_residual.source_cocycle
    {
        examples.push(generic_validation_example(
            &format!("{prefix}.presentationGenerated"),
            "established-evidence",
            "established presentation-generated comparison requires all generated exactness, naturality, cocycle, and cochain-map checks",
        ));
    }

    let degree_zero_refs = check_saga_derived_cell_rows(
        &presentation.generated_cochain_map.degree_zero,
        &format!("{prefix}.presentationGenerated.generatedCochainMap.degreeZero"),
        examples,
    );
    let degree_one_refs = check_saga_derived_cell_rows(
        &presentation.generated_cochain_map.degree_one,
        &format!("{prefix}.presentationGenerated.generatedCochainMap.degreeOne"),
        examples,
    );
    check_saga_derived_cell_rows(
        &presentation.generated_cochain_map.degree_two,
        &format!("{prefix}.presentationGenerated.generatedCochainMap.degreeTwo"),
        examples,
    );

    let Some(source_class_nonzero) = presentation.semantic_residual.source_class_nonzero else {
        examples.push(generic_validation_example(
            &format!("{prefix}.presentationGenerated.semanticResidual.sourceClassNonZero"),
            "boolean",
            "established presentation-generated comparison requires a computed source H1 class",
        ));
        return;
    };
    let Some(target_class_nonzero) = presentation.equation_residual.target_class_nonzero else {
        examples.push(generic_validation_example(
            &format!("{prefix}.presentationGenerated.equationResidual.targetClassNonZero"),
            "boolean",
            "established presentation-generated comparison requires a computed target H1 class",
        ));
        return;
    };
    let Some(witness) = presentation.residual_witness.as_ref() else {
        examples.push(generic_validation_example(
            &format!("{prefix}.presentationGenerated.residualWitness"),
            "required",
            "established presentation-generated comparison requires a computed quotient-atlas witness",
        ));
        return;
    };
    check_saga_residual_witness(
        witness,
        &format!("{prefix}.presentationGenerated.residualWitness"),
        &degree_zero_refs,
        &degree_one_refs,
        examples,
    );

    let transfer_value = &invariant["generatedQuotientTransfer"];
    let transfer_fields = [
        "level",
        "kind",
        "preservesZeroPredicate",
        "sourceClassNonZero",
        "targetClassNonZero",
        "sourceInvariant",
        "targetInvariant",
    ];
    if !check_required_object_keys(
        transfer_value,
        &format!("{prefix}.generatedQuotientTransfer"),
        &transfer_fields,
        examples,
    ) {
        return;
    }
    let transfer = match serde_json::from_value::<SagaGeneratedQuotientTransferEvidenceV1>(
        transfer_value.clone(),
    ) {
        Ok(transfer) => transfer,
        Err(error) => {
            examples.push(generic_validation_example(
                &format!("{prefix}.generatedQuotientTransfer"),
                "typed-shape",
                &format!(
                    "established presentation-generated quotient transfer must have the documented typed shape: {error}"
                ),
            ));
            return;
        }
    };
    if transfer.level != "quotient"
        || transfer.kind != "presentation-derived-Z1/B1-class-transfer"
        || !transfer.preserves_zero_predicate
        || transfer.source_invariant != "presentation-generated:semantic-h1-class"
        || transfer.target_invariant != "saga-comparison:h1-transfer"
        || transfer.source_class_nonzero != source_class_nonzero
        || transfer.target_class_nonzero != target_class_nonzero
    {
        examples.push(generic_validation_example(
            &format!("{prefix}.generatedQuotientTransfer"),
            "presentation-consistency",
            "generated quotient transfer must preserve the computed presentation source and target H1 classes",
        ));
    }
}

fn check_saga_derived_cell_rows(
    rows: &[SagaDerivedCellEvidenceV1],
    path: &str,
    examples: &mut Vec<ValidationExample>,
) -> BTreeSet<String> {
    let refs = rows
        .iter()
        .map(|row| row.cell_ref.clone())
        .collect::<BTreeSet<_>>();
    if refs.len() != rows.len()
        || rows.iter().any(|row| {
            row.cell_ref.is_empty()
                || row.local_phi_derived_from != "generatorMap modulo repair/equation relations"
        })
    {
        examples.push(generic_validation_example(
            path,
            "derived-cell-rows",
            "derived cochain-map rows require unique nonempty cellRef values and local Phi provenance",
        ));
    }
    refs
}

fn check_saga_residual_witness(
    witness: &SagaResidualWitnessEvidenceV1,
    path: &str,
    degree_zero_refs: &BTreeSet<String>,
    degree_one_refs: &BTreeSet<String>,
    examples: &mut Vec<ValidationExample>,
) {
    if witness.kind != "computed-quotient-atlas-witness"
        || witness.equation != "kappa1(r_sem) = r_E + delta0(h)"
        || !witness.difference_is_delta_zero
    {
        examples.push(generic_validation_example(
            path,
            "witness-contract",
            "computed quotient-atlas witness must retain its equation and delta-zero conclusion",
        ));
    }
    let source_refs = check_saga_equation_cochain_rows(
        &witness.source_image,
        &format!("{path}.sourceImage"),
        examples,
    );
    let residual_refs = check_saga_equation_cochain_rows(
        &witness.equation_residual,
        &format!("{path}.equationResidual"),
        examples,
    );
    let chart_refs = check_saga_equation_chart_rows(&witness.h, &format!("{path}.h"), examples);
    if &source_refs != degree_one_refs
        || &residual_refs != degree_one_refs
        || &chart_refs != degree_zero_refs
    {
        examples.push(generic_validation_example(
            path,
            "witness-cell-coverage",
            "computed quotient-atlas witness must cover exactly the generated degree-one and degree-zero cells",
        ));
    }
}

fn check_saga_equation_cochain_rows(
    rows: &[SagaEquationCochainEvidenceV1],
    path: &str,
    examples: &mut Vec<ValidationExample>,
) -> BTreeSet<String> {
    let refs = rows
        .iter()
        .map(|row| row.overlap_ref.clone())
        .collect::<BTreeSet<_>>();
    if refs.len() != rows.len()
        || rows.iter().any(|row| {
            row.overlap_ref.is_empty()
                || row.equation_generators.is_empty()
                || row.equation_generators.len() != row.coefficients.len()
                || row.coefficients.iter().any(|coefficient| *coefficient > 1)
        })
    {
        examples.push(generic_validation_example(
            path,
            "F2-cochain-rows",
            "computed witness cochain rows require unique overlapRef values, aligned generators, and F2 coefficients",
        ));
    }
    refs
}

fn check_saga_equation_chart_rows(
    rows: &[SagaEquationChartAssignmentEvidenceV1],
    path: &str,
    examples: &mut Vec<ValidationExample>,
) -> BTreeSet<String> {
    let refs = rows
        .iter()
        .map(|row| row.chart_ref.clone())
        .collect::<BTreeSet<_>>();
    if refs.len() != rows.len()
        || rows.iter().any(|row| {
            row.chart_ref.is_empty()
                || row.equation_generators.is_empty()
                || row.equation_generators.len() != row.coefficients.len()
                || row.coefficients.iter().any(|coefficient| *coefficient > 1)
        })
    {
        examples.push(generic_validation_example(
            path,
            "F2-chart-rows",
            "computed witness chart rows require unique chartRef values, aligned generators, and F2 coefficients",
        ));
    }
    refs
}

fn validate_saga_grounded_packet_shape(
    invariant: &Value,
    label: &str,
    examples: &mut Vec<ValidationExample>,
) {
    for field in [
        "schema",
        "groundedSurfaceRef",
        "theoremRef",
        "lawDependent",
        "lawIndependent",
        "degreeZeroLawContribution",
        "generatedQuotient",
        "detectorFindings",
    ] {
        if invariant.get(field).is_none() {
            examples.push(generic_validation_example(
                label,
                field,
                "saga-grounded conclusion packet requires all typed top-level sections",
            ));
        }
    }
    if invariant["schema"].as_str() != Some("archsig-saga-conclusions/v0.5.4") {
        examples.push(generic_validation_example(
            &format!("{label}.schema"),
            invariant["schema"].as_str().unwrap_or("missing"),
            "saga-grounded packet schema must be archsig-saga-conclusions/v0.5.4",
        ));
    }
    let detector_findings = invariant["detectorFindings"].as_array();
    let detector_count = invariant["detectorCount"].as_u64();
    if detector_count.is_none() {
        examples.push(generic_validation_example(
            &format!("{label}.detectorCount"),
            "missing-or-non-integer",
            "saga-grounded detectorCount must be a non-negative integer",
        ));
    } else if detector_findings
        .is_some_and(|findings| detector_count != Some(findings.len() as u64))
    {
        examples.push(generic_validation_example(
            &format!("{label}.detectorCount"),
            &detector_count.unwrap_or_default().to_string(),
            "saga-grounded detectorCount must equal detectorFindings length",
        ));
    }
    for (section, expected) in [
        (
            "lawDependent",
            [
                "generatedInterpretationZero",
                "generatedRestrictionEvaluator",
                "nonzeroInterpretationDetectsDisplayedLawFailure",
            ]
            .as_slice(),
        ),
        (
            "lawIndependent",
            [
                "groundedGlobalGluingPackage",
                "sheafConditionForSelectedCover",
                "descent",
                "uniqueGlobalSection",
                "globalCoherentIffCoverRelativeH1Zero",
                "boundedAdditiveH1ZeroIffCoverRelativeH1Zero",
                "higherObstructionsVanish",
            ]
            .as_slice(),
        ),
    ] {
        let conclusions = &invariant[section]["conclusions"];
        if !conclusions.is_object() {
            examples.push(generic_validation_example(
                &format!("{label}.{section}"),
                "missing",
                "grounded conclusion section must carry a conclusions object",
            ));
            continue;
        }
        check_object_keys(
            conclusions,
            &format!("{label}.{section}.conclusions"),
            expected,
            examples,
        );
        for conclusion in expected.iter().copied() {
            let row = &conclusions[conclusion];
            if row["status"].as_str().is_none() || row["theoremRef"].as_str().is_none() {
                examples.push(generic_validation_example(
                    &format!("{label}.{section}.conclusions.{conclusion}"),
                    "status/theoremRef",
                    "each grounded conclusion must carry status and theoremRef",
                ));
            }
        }
    }
    let quotient = &invariant["generatedQuotient"];
    for field in [
        "ambient",
        "obstructionIdeal",
        "representative",
        "interpretation",
    ] {
        if quotient.get(field).is_none() {
            examples.push(generic_validation_example(
                &format!("{label}.generatedQuotient"),
                field,
                "generated quotient must expose ambient, obstruction ideal, representative, and interpretation",
            ));
        }
    }
    if quotient["coefficient"].as_str() != Some("F2")
        || quotient["finiteBoundChecked"].as_bool() != Some(true)
        || quotient["finiteBound"].as_u64().is_none()
    {
        examples.push(generic_validation_example(
            &format!("{label}.generatedQuotient"),
            "coefficient/finiteBoundChecked",
            "generated quotient must record F2 and a checked finite bound",
        ));
    }
    let Some(ambient_basis) = quotient["ambient"]["basis"].as_array() else {
        examples.push(generic_validation_example(
            &format!("{label}.generatedQuotient.ambient.basis"),
            "not-array",
            "generated quotient ambient basis must be an array of strings",
        ));
        return;
    };
    let ambient_basis = ambient_basis
        .iter()
        .filter_map(Value::as_str)
        .collect::<BTreeSet<_>>();
    if ambient_basis.is_empty() {
        examples.push(generic_validation_example(
            &format!("{label}.generatedQuotient.ambient.basis"),
            "empty",
            "generated quotient ambient basis must contain the supplied witness variables",
        ));
    }
    if quotient["ambient"]["relations"].as_array().is_none() {
        examples.push(generic_validation_example(
            &format!("{label}.generatedQuotient.ambient.relations"),
            "missing",
            "generated quotient ambient relations must be recorded",
        ));
    }
    let Some(generators) = quotient["obstructionIdeal"]["generators"].as_array() else {
        examples.push(generic_validation_example(
            &format!("{label}.generatedQuotient.obstructionIdeal.generators"),
            "not-array",
            "generated obstruction ideal generators must be an array",
        ));
        return;
    };
    for (index, generator) in generators.iter().enumerate() {
        let generator_label =
            format!("{label}.generatedQuotient.obstructionIdeal.generators[{index}]");
        for field in ["generatorId", "support", "supportAtomRefs"] {
            if generator[field].is_null() {
                examples.push(generic_validation_example(
                    &generator_label,
                    field,
                    "generated obstruction ideal generators must expose typed support fields",
                ));
            }
        }
        if generator["generatorId"].as_str().is_none_or(str::is_empty)
            || generator["support"].as_array().is_none_or(|support| {
                support.is_empty()
                    || support.iter().any(|variable| {
                        variable
                            .as_str()
                            .is_none_or(|variable| !ambient_basis.contains(variable))
                    })
            })
            || generator["supportAtomRefs"]
                .as_array()
                .is_none_or(|refs| refs.iter().any(|reference| reference.as_str().is_none()))
        {
            examples.push(generic_validation_example(
                &generator_label,
                "support",
                "generated obstruction ideal support must be nonempty and contained in the ambient basis",
            ));
        }
    }
    let Some(representative) = quotient["representative"].as_object() else {
        examples.push(generic_validation_example(
            &format!("{label}.generatedQuotient.representative"),
            "missing",
            "generated quotient representative must be an object",
        ));
        return;
    };
    let support = representative.get("support").and_then(Value::as_array);
    let normal_form = representative.get("normalForm").and_then(Value::as_array);
    if support.is_none()
        || normal_form.is_none()
        || support != normal_form
        || support.is_some_and(|support| {
            support.iter().any(|variable| {
                variable
                    .as_str()
                    .is_none_or(|variable| !ambient_basis.contains(variable))
            })
        })
    {
        examples.push(generic_validation_example(
            &format!("{label}.generatedQuotient.representative"),
            "support/normalForm",
            "generated quotient representative must be a normalized ambient-basis support",
        ));
    }
    let Some(interpretation) = quotient["interpretation"].as_object() else {
        examples.push(generic_validation_example(
            &format!("{label}.generatedQuotient.interpretation"),
            "missing",
            "generated quotient interpretation must be an object",
        ));
        return;
    };
    if !matches!(
        interpretation.get("class").and_then(Value::as_str),
        Some("zero" | "nonzero")
    ) || interpretation
        .get("map")
        .and_then(Value::as_array)
        .is_none()
        || interpretation
            .get("representative")
            .and_then(Value::as_array)
            .is_none()
    {
        examples.push(generic_validation_example(
            &format!("{label}.generatedQuotient.interpretation"),
            "map/class/representative",
            "generated quotient interpretation must expose a typed map, class, and representative",
        ));
    }
    if let Some(map) = interpretation.get("map").and_then(Value::as_array) {
        if map.len() != ambient_basis.len()
            || map.iter().any(|entry| {
                let Some(entry) = entry.as_object() else {
                    return true;
                };
                entry
                    .get("variable")
                    .and_then(Value::as_str)
                    .is_none_or(|variable| !ambient_basis.contains(variable))
                    || entry.get("image").and_then(Value::as_str).is_none()
                    || entry.get("observed").and_then(Value::as_bool).is_none()
            })
        {
            examples.push(generic_validation_example(
                &format!("{label}.generatedQuotient.interpretation.map"),
                "invalid",
                "generated quotient interpretation map must cover each ambient witness variable",
            ));
        }
    }
    if !invariant["detectorFindings"].is_array() {
        examples.push(generic_validation_example(
            &format!("{label}.detectorFindings"),
            "not-array",
            "detectorFindings must be an array",
        ));
    } else if let Some(findings) = invariant["detectorFindings"].as_array() {
        for (index, finding) in findings.iter().enumerate() {
            let finding_label = format!("{label}.detectorFindings[{index}]");
            if ["chart", "law", "interpretationClass", "reading"]
                .iter()
                .any(|field| finding[*field].as_str().is_none_or(str::is_empty))
            {
                examples.push(generic_validation_example(
                    &finding_label,
                    "typed-fields",
                    "detector findings must identify chart, law, interpretation class, and reading",
                ));
            }
        }
    }
}

fn check_analytic_regime_boundary(
    packet: &ArchSigMeasurementPacketV1,
    packet_value: &Value,
) -> ValidationCheck {
    let structural_evaluators = packet
        .structural_verdict
        .iter()
        .map(|row| row.evaluator.as_str())
        .collect::<BTreeSet<_>>();
    let structural_refs = packet_value["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|row| row["verdictRef"].as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    for (index, reading_value) in packet_value["analyticReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let label = format!("analyticReadings[{index}]");
        let claim_status = reading_value["claimStatus"].as_str().unwrap_or_default();
        if !matches!(claim_status, "certified" | "candidate") {
            examples.push(generic_validation_example(
                &label,
                claim_status,
                "analytic reading claimStatus must be certified or candidate",
            ));
        }
        let fidelity = reading_value["fidelity"].as_str().unwrap_or_default();
        if !matches!(fidelity, "faithful" | "proxy") {
            examples.push(generic_validation_example(
                &label,
                fidelity,
                "analytic reading fidelity must be faithful or proxy",
            ));
        }
        if let Some(reading) = packet.analytic_readings.get(index) {
            let expected_claim_status = analytic_claim_status(reading);
            if claim_status != expected_claim_status {
                examples.push(generic_validation_example(
                    &label,
                    claim_status,
                    &format!(
                        "authored analytic reading claimStatus must match derived value {expected_claim_status}"
                    ),
                ));
            }
            let expected_fidelity = analytic_fidelity(reading);
            if fidelity != expected_fidelity {
                examples.push(generic_validation_example(
                    &label,
                    fidelity,
                    &format!(
                        "authored analytic reading fidelity must match derived value {expected_fidelity}"
                    ),
                ));
            }
        }
        if claim_status == "candidate" && !reading_value["structuralVerdictRef"].is_null() {
            examples.push(generic_validation_example(
                &label,
                "structuralVerdictRef",
                "candidate readings must remain analytic-only",
            ));
        }
        if claim_status != "candidate"
            && let Some(structural_ref) = reading_value["structuralVerdictRef"].as_str()
            && !structural_refs.contains(structural_ref)
        {
            examples.push(generic_validation_example(
                &label,
                structural_ref,
                "certified analytic reading structuralVerdictRef must resolve to a structural verdict",
            ));
        }
        if reading_value["evaluator"] == "ag.harmonic-debt"
            && reading_value["value"]["lowerBoundStatus"] == "cost_model_not_supplied"
        {
            let next_input = reading_value["value"]["whatNext"].as_str();
            if next_input.is_none_or(|text| text.trim().is_empty()) {
                examples.push(generic_validation_example(
                    &label,
                    "value.whatNext",
                    "harmonic cost-model silence must expose the next required input",
                ));
            }
            let matching_invariant = packet_value["computedInvariants"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|invariant| invariant["evaluator"] == "ag.harmonic-debt");
            if matching_invariant.is_none_or(|invariant| {
                invariant["status"] != "silence_by_design"
                    || invariant["whatNext"].as_str() != next_input
            }) {
                examples.push(generic_validation_example(
                    &label,
                    "value.whatNext",
                    "harmonic cost-model silence must match the computed invariant whatNext guidance",
                ));
            }
        }
    }
    for reading in &packet.analytic_readings {
        if reading
            .regime
            .as_deref()
            .is_some_and(|regime| regime.contains("candidate"))
            && reading.structural_verdict_ref.is_some()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "structuralVerdictRef",
                "theorem-candidate readings must remain analytic-only",
            ));
        }
        if reading
            .regime
            .as_deref()
            .is_some_and(|regime| regime.contains("candidate"))
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
        "measurement-packet-schema052-theorem-candidate-analytic-only",
        "theorem-candidate readings are flagged analytic readings and do not generate structural verdicts",
        examples,
    )
}

fn check_supplied_data_shape(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let packet_value = serde_json::to_value(packet).unwrap_or_else(|_| json!({}));
    let mut examples = Vec::new();
    if !packet_value["suppliedData"].is_array() {
        examples.push(generic_validation_example(
            "suppliedData",
            "missing",
            "measurement packet must expose suppliedData ledger",
        ));
    } else if packet_value["suppliedData"]
        .as_array()
        .is_some_and(Vec::is_empty)
    {
        examples.push(generic_validation_example(
            "suppliedData",
            "empty",
            "measurement packet must record supplied input artifacts",
        ));
    }
    let mut supplied_kinds = BTreeSet::new();
    let mut supplied_ids = BTreeSet::new();
    for (index, supplied) in packet_value["suppliedData"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let label = format!("suppliedData[{index}]");
        if let Some(supplied_id) = supplied["suppliedId"].as_str() {
            if !supplied_ids.insert(supplied_id) {
                examples.push(generic_validation_example(
                    &label,
                    supplied_id,
                    "suppliedData suppliedId values must be unique",
                ));
            }
        }
        for field in ["suppliedId", "kind", "sourceArtifactRef"] {
            if supplied[field].as_str().is_none_or(str::is_empty) {
                examples.push(generic_validation_example(
                    &label,
                    field,
                    "suppliedData entries must carry suppliedId / kind / sourceArtifactRef",
                ));
            }
        }
        if let Some(kind) = supplied["kind"].as_str() {
            if !supplied_kinds.insert(kind) {
                examples.push(generic_validation_example(
                    &label,
                    kind,
                    "suppliedData kind values must be unique",
                ));
            }
            if !matches!(
                kind,
                "archmap"
                    | "law-policy"
                    | "law-equation-surface"
                    | "measurement-profile"
                    | "repair-plan"
                    | "residual-packet"
            ) {
                examples.push(generic_validation_example(
                    &label,
                    kind,
                    "suppliedData kind must be one of the input artifact ledger kinds",
                ));
            }
        }
        if !supplied["conformance"].is_object() {
            examples.push(generic_validation_example(
                &label,
                "conformance",
                "suppliedData entries must carry conformance object",
            ));
        } else if supplied["conformance"]["status"]
            .as_str()
            .is_none_or(|status| !matches!(status, "validated" | "assumed" | "derived"))
        {
            examples.push(generic_validation_example(
                &label,
                "conformance.status",
                "suppliedData conformance status must be validated, assumed, or derived",
            ));
        } else if supplied["conformance"]["checkRef"]
            .as_str()
            .is_none_or(str::is_empty)
        {
            examples.push(generic_validation_example(
                &label,
                "conformance.checkRef",
                "suppliedData conformance must carry a non-empty checkRef",
            ));
        }
    }
    for required_kind in ["archmap", "law-policy", "measurement-profile"] {
        if !supplied_kinds.contains(required_kind) {
            examples.push(generic_validation_example(
                "suppliedData",
                required_kind,
                "measurement packet suppliedData must ledger archmap, law-policy, and measurement-profile inputs",
            ));
        }
    }
    check_examples(
        "measurement-packet-schema052-supplied-data-ledger",
        "suppliedData ledger is present and typed when entries exist",
        examples,
    )
}

fn check_assumption_ledger(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let assumption_refs = packet
        .assumptions
        .iter()
        .map(assumption_id_for_schema)
        .collect::<BTreeSet<_>>();
    let violated = packet
        .assumptions
        .iter()
        .filter(|entry| entry.status == "violated")
        .map(assumption_id_for_schema)
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    let mut authored_assumption_ids = BTreeSet::new();
    for entry in &packet.assumptions {
        let derived_id = assumption_id_for_schema(entry);
        if !authored_assumption_ids.insert(derived_id.clone()) {
            examples.push(generic_validation_example(
                &entry.theorem_ref,
                &derived_id,
                "assumptionId values must be unique",
            ));
        }
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
    for row in &packet.structural_verdict {
        for theorem_ref in &row.depends_on_assumptions {
            if !assumption_refs.contains(theorem_ref) {
                examples.push(generic_validation_example(
                    &row.evaluator,
                    theorem_ref,
                    "dependsOnAssumptions entries must resolve to assumptionId values",
                ));
            }
        }
        if is_measured_verdict(&row.verdict)
            && row
                .depends_on_assumptions
                .iter()
                .any(|theorem_ref| violated.contains(theorem_ref))
        {
            examples.push(generic_validation_example(
                &row.evaluator,
                &row.verdict,
                "measured structural verdicts must not depend on violated assumptions",
            ));
        }
    }
    check_examples(
        "measurement-packet-schema052-assumption-ledger",
        "assumption ledger records checked / assumed / violated and row-level verdict dependencies",
        examples,
    )
}

fn check_assumption_ledger_value(
    packet: &ArchSigMeasurementPacketV1,
    packet_value: &Value,
) -> ValidationCheck {
    let mut check = check_assumption_ledger(packet);
    let mut raw_examples = Vec::new();
    for (index, assumption) in packet_value["assumptions"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let label = format!("assumptions[{index}]");
        let expected_id = packet
            .assumptions
            .get(index)
            .map(assumption_id_for_schema)
            .unwrap_or_default();
        let authored_id = assumption["assumptionId"].as_str();
        if authored_id.is_none_or(str::is_empty) {
            raw_examples.push(generic_validation_example(
                &label,
                "assumptionId",
                "assumption entries must carry authored assumptionId; theoremRef is not a fallback",
            ));
        } else if authored_id != Some(expected_id.as_str()) {
            raw_examples.push(generic_validation_example(
                &label,
                authored_id.unwrap_or_default(),
                &format!("authored assumptionId must match derived value {expected_id}"),
            ));
        }
    }
    if !raw_examples.is_empty() {
        check.result = "fail".to_string();
        check.examples.extend(raw_examples);
        check.count = Some(check.examples.len());
    }
    check
}

fn check_boundary_statements(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let mut examples = Vec::new();
    let mut ids = BTreeSet::new();
    let valid_scope_refs = measurement_packet_scope_refs(packet);
    let boundary_texts = packet
        .boundary_statements
        .iter()
        .map(|statement| statement.text.as_str())
        .collect::<BTreeSet<_>>();

    if packet.boundary_statements.is_empty() {
        examples.push(generic_validation_example(
            "boundaryStatements",
            "empty",
            "measurement packet must expose typed boundary statements",
        ));
    }

    for statement in &packet.boundary_statements {
        if statement.id.trim().is_empty() {
            examples.push(generic_validation_example(
                "boundaryStatements[].id",
                "empty",
                "boundary statement id must be non-empty",
            ));
        } else if !ids.insert(statement.id.as_str()) {
            examples.push(generic_validation_example(
                "boundaryStatements[].id",
                &statement.id,
                "boundary statement id must be unique",
            ));
        }
        if !BOUNDARY_STATEMENT_KINDS.contains(&statement.kind.as_str()) {
            examples.push(generic_validation_example(
                &statement.id,
                &statement.kind,
                "boundary statement kind must be one of the v0.5.4 boundary kinds",
            ));
        }
        if statement.reason.trim().is_empty() {
            examples.push(generic_validation_example(
                &statement.id,
                "reason",
                "boundary statement reason must be non-empty",
            ));
        }
        if statement.text.trim().is_empty() {
            examples.push(generic_validation_example(
                &statement.id,
                "text",
                "boundary statement text must be non-empty",
            ));
        }
        if statement.scope_refs.is_empty() {
            examples.push(generic_validation_example(
                &statement.id,
                "scopeRefs",
                "boundary statement scopeRefs must be non-empty",
            ));
        }
        for scope_ref in &statement.scope_refs {
            if !valid_scope_refs.contains(scope_ref) {
                examples.push(generic_validation_example(
                    &statement.id,
                    scope_ref,
                    "boundary statement scopeRefs must resolve inside the measurement packet",
                ));
            }
        }
        if statement.kind == "violated_assumption"
            && !statement
                .scope_refs
                .iter()
                .any(|scope_ref| blocked_measurement_scope_refs(packet).contains(scope_ref))
        {
            examples.push(generic_validation_example(
                &statement.id,
                "scopeRefs",
                "violated_assumption boundary must scope to a not_computed or unmeasured packet surface",
            ));
        }
        if statement.kind == "silence_by_design"
            && statement.scope_refs.iter().any(|scope_ref| {
                packet.structural_verdict.iter().any(|row| {
                    structural_verdict_ref(row) == *scope_ref && row.verdict == "measured_nonzero"
                })
            })
        {
            examples.push(generic_validation_example(
                &statement.id,
                "scopeRefs",
                "silence_by_design boundary must not scope to a measured_nonzero structural verdict",
            ));
        }
    }

    for invariant in &packet.computed_invariants {
        let invariant_id = invariant["invariantId"].as_str().unwrap_or_default();
        let status = invariant["status"].as_str();
        if invariant.get("whatNext").is_some() && status != Some("silence_by_design") {
            examples.push(generic_validation_example(
                invariant_id,
                "whatNext",
                "whatNext is reserved for silence_by_design invariants",
            ));
        }
        if status.is_some() && status != Some("silence_by_design") {
            if packet.boundary_statements.iter().any(|statement| {
                statement.kind == "silence_by_design"
                    && statement
                        .scope_refs
                        .iter()
                        .any(|scope_ref| scope_ref == invariant_id)
            }) {
                examples.push(generic_validation_example(
                    invariant_id,
                    "boundaryStatements",
                    "typed silence boundaries must not scope to a non-silence invariant",
                ));
            }
        }
        if invariant.get("whatNext").is_some() {
            let Some(what_next) = invariant["whatNext"].as_str() else {
                examples.push(generic_validation_example(
                    invariant["invariantId"]
                        .as_str()
                        .unwrap_or("computed-invariant"),
                    "whatNext",
                    "whatNext must be a non-empty string when supplied",
                ));
                continue;
            };
            if what_next.trim().is_empty() {
                examples.push(generic_validation_example(
                    invariant["invariantId"]
                        .as_str()
                        .unwrap_or("computed-invariant"),
                    "whatNext",
                    "whatNext must be a non-empty string when supplied",
                ));
            }
        }
        if invariant["status"].as_str() == Some("silence_by_design") {
            if invariant["whatNext"]
                .as_str()
                .is_none_or(|text| text.trim().is_empty())
            {
                examples.push(generic_validation_example(
                    invariant_id,
                    "whatNext",
                    "silence_by_design invariants must explain the next required input",
                ));
            }
            if !packet.boundary_statements.iter().any(|statement| {
                statement.kind == "silence_by_design"
                    && statement
                        .scope_refs
                        .iter()
                        .any(|scope_ref| scope_ref == invariant_id)
            }) {
                examples.push(generic_validation_example(
                    invariant_id,
                    "boundaryStatements",
                    "silence_by_design invariants must have a typed boundary scoped to the invariant",
                ));
            } else if let Some(statement) = packet.boundary_statements.iter().find(|statement| {
                statement.kind == "silence_by_design"
                    && statement
                        .scope_refs
                        .iter()
                        .any(|scope_ref| scope_ref == invariant_id)
            }) {
                let what_next = invariant["whatNext"].as_str().unwrap_or_default();
                if !statement.text.contains(what_next) {
                    examples.push(generic_validation_example(
                        invariant_id,
                        "boundaryStatements.text",
                        "typed silence boundary text must include the invariant whatNext guidance",
                    ));
                }
            }
        }
    }

    for text in &packet.non_conclusions {
        if !boundary_texts.contains(text.as_str()) {
            examples.push(generic_validation_example(
                "nonConclusions",
                text,
                "compat nonConclusions text must be reproduced by boundaryStatements[].text",
            ));
        }
    }

    check_examples(
        "measurement-packet-schema052-boundary-statements",
        "boundaryStatements provide typed, scoped non-conclusion qualifiers with nonConclusions compatibility",
        examples,
    )
}

fn measurement_packet_scope_refs(packet: &ArchSigMeasurementPacketV1) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    refs.insert(packet.packet_id.clone());
    refs.extend(
        packet
            .analytic_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    refs.extend(packet.assumptions.iter().map(assumption_id_for_schema));
    refs.extend(
        packet
            .supplied_data
            .iter()
            .map(|entry| entry.supplied_id.clone()),
    );
    for row in &packet.structural_verdict {
        refs.insert(row.evaluator.clone());
        refs.insert(row.law.clone());
        refs.insert(structural_verdict_ref(row));
    }
    for invariant in &packet.computed_invariants {
        for field in ["id", "invariantId", "readingId", "computedInvariantId"] {
            if let Some(value) = invariant.get(field).and_then(Value::as_str) {
                refs.insert(value.to_string());
            }
        }
    }
    refs
}

fn not_computed_scope_refs(packet: &ArchSigMeasurementPacketV1) -> BTreeSet<String> {
    let mut refs = packet
        .structural_verdict
        .iter()
        .filter(|row| row.verdict == "not_computed")
        .map(structural_verdict_ref)
        .collect::<BTreeSet<_>>();
    refs.extend(packet.analytic_readings.iter().filter_map(|reading| {
        (reading.value.get("status").and_then(Value::as_str) == Some("not_computed"))
            .then(|| reading.reading_id.clone())
    }));
    for invariant in &packet.computed_invariants {
        if invariant.get("status").and_then(Value::as_str) == Some("not_computed") {
            for field in ["id", "invariantId", "readingId", "computedInvariantId"] {
                if let Some(value) = invariant.get(field).and_then(Value::as_str) {
                    refs.insert(value.to_string());
                    break;
                }
            }
        }
    }
    refs
}

fn blocked_measurement_scope_refs(packet: &ArchSigMeasurementPacketV1) -> BTreeSet<String> {
    let mut refs = not_computed_scope_refs(packet);
    refs.extend(
        packet
            .structural_verdict
            .iter()
            .filter(|row| row.verdict == "unmeasured")
            .map(structural_verdict_ref),
    );
    for invariant in &packet.computed_invariants {
        if invariant.get("status").and_then(Value::as_str) == Some("unmeasured") {
            for field in ["id", "invariantId", "readingId", "computedInvariantId"] {
                if let Some(value) = invariant.get(field).and_then(Value::as_str) {
                    refs.insert(value.to_string());
                    break;
                }
            }
        }
    }
    refs
}

fn dependent_blocked_measurement_scope_refs(
    packet: &ArchSigMeasurementPacketV1,
    theorem_ref: &str,
) -> Vec<String> {
    packet
        .structural_verdict
        .iter()
        .filter(|row| {
            matches!(row.verdict.as_str(), "not_computed" | "unmeasured")
                && row
                    .depends_on_assumptions
                    .iter()
                    .any(|dependency| dependency == theorem_ref)
        })
        .map(structural_verdict_ref)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
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
        let mut packet: ArchSigMeasurementPacketV1 = serde_json::from_value(json!({
            "schema": "archsig-measurement-packet/v0.5.4",
            "packetId": "measurement:test",
            "profile": {
                "schema": "measurement-profile/v0.5.4",
                "profileId": "profile:test",
                "siteRef": "archmap:/contexts",
                "coverRef": "cover:test",
                "coefficient": "F2",
                "effCoeff": "finite-linear-algebra@1",
                "resolutionSelector": "taylor@1",
                "domain": "finite-poset-site",
                "zeroPredicate": "rank-zero@1",
                "nonZeroPredicate": "rank-positive@1",
                "certSelector": "finite-certificate@1",
                "verdictDiscipline": "five-valued-structural-verdict@1",
                "finiteBounds": {
                    "maxSquareFreeWitnessVariables": 12,
                    "maxCoherenceContexts": 12,
                    "maxTorWitnessVariables": 12,
                    "maxBoundaryResidueVariables": 16,
                    "maxLaplacianCells": 16,
                    "maxPeriodCycles": 16,
                    "maxTransferTargets": 16
                }
            },
            "structuralVerdict": [{
                "evaluator": "ag.cech-obstruction",
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
                "evaluator": "ag.foundation",
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
            "suppliedData": [{
                "suppliedId": "supplied:archmap",
                "kind": "archmap",
                "sourceArtifactRef": "input:archmap.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "archmap/v0.5.4-validation"
                }
            }, {
                "suppliedId": "supplied:law-policy",
                "kind": "law-policy",
                "sourceArtifactRef": "input:law-policy.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "law-policy/v0.5.4-validation"
                }
            }, {
                "suppliedId": "supplied:measurement-profile",
                "kind": "measurement-profile",
                "sourceArtifactRef": "input:measurement-profile.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "measurement-profile/v0.5.4-validation"
                }
            }],
            "nonConclusions": ["test fixture"]
        }))
        .expect("packet fixture parses");
        packet.boundary_statements = boundary_statements_for_measurement_packet(&packet);
        packet
    }

    fn normalized_fixture() -> NormalizedArchMapV2 {
        serde_json::from_value(json!({
            "schema": "archmap-normalized/v0.5.4",
            "normalizerId": "test-normalizer",
            "sourceArchmapRef": "archmap:test",
            "sourceArchmapId": "archmap:test",
            "extractionDoctrineRef": {
                "doctrineId": "doctrine:aat-canonical@1",
                "fingerprint": "sha256:aat-canonical-doctrine-schema052",
                "components": ["V", "Gamma", "R", "rho", "E", "N"]
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
                "doctrineFingerprint": "sha256:aat-canonical-doctrine-schema052"
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
            check.id == "measurement-packet-schema052-five-verdict-values" && check.result == "fail"
        }));
    }

    #[test]
    fn unregistered_structural_verdict_evaluator_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].evaluator = "ag.synthetic-new-verdict".to_string();
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-structural-verdict-evaluators"
                && check.result == "fail"
        }));
    }

    #[test]
    fn unknown_computed_invariant_kind_fails_validation() {
        let mut packet = packet_fixture();
        packet.computed_invariants.push(json!({
            "invariantId": "invariant:unknown-kind",
            "kind": "unregistered-freeform-kind",
            "value": 1,
            "representation": {"basis": "test"}
        }));
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-computed-invariants-typed"
                && check.result == "fail"
        }));
    }

    #[test]
    fn empty_supplied_data_ledger_fails_validation() {
        let mut packet = packet_fixture();
        packet.supplied_data.clear();
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-supplied-data-ledger"
                && check.result == "fail"
        }));
    }

    #[test]
    fn zero_and_nonzero_verdict_data_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].verdict_data.non_zero = true;
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-verdict-data-boundary"
                && check.result == "fail"
        }));
    }

    #[test]
    fn measured_zero_requires_unhedged_verdict_data() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict = "measured_zero".to_string();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].verdict_data.in_scope = false;
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-verdict-data-boundary"
                && check.result == "fail"
        }));

        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict = "measured_zero".to_string();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].verdict_data.non_zero = true;
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-verdict-data-boundary"
                && check.result == "fail"
        }));
    }

    #[test]
    fn measured_verdict_depending_on_violated_assumption_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict = "measured_zero".to_string();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].depends_on_assumptions =
            vec![assumption_id_for_schema(&packet.assumptions[0])];
        packet.assumptions[0].status = "violated".to_string();
        packet.assumptions[0].checked_by = None;
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-assumption-ledger" && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_measured_zero_with_empty_scope_fails_raw_validation() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["structuralVerdict"][0]["verdict"] = json!("measured_zero");
        raw["structuralVerdict"][0]["verdictData"]["inScope"] = json!(true);
        raw["structuralVerdict"][0]["verdictData"]["zero"] = json!(true);
        raw["structuralVerdict"][0]["target"]["scopeSize"] =
            json!({"contexts": 0, "edges": 0, "triangles": 0});
        raw["structuralVerdict"][0]["evidence"]["computedInvariantRefs"] = json!([]);

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-structural-verdict-new-shape"
                && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_structural_evidence_shape_rejects_missing_and_non_string_refs() {
        let packet = packet_fixture();
        let mut missing_evidence = serde_json::to_value(&packet).expect("packet serializes");
        missing_evidence["structuralVerdict"][0]
            .as_object_mut()
            .unwrap()
            .remove("evidence");
        let checks = validate_measurement_packet_value_v1(&missing_evidence);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-structural-verdict-new-shape"
                && check.result == "fail"
        }));

        let mut non_string_ref = serde_json::to_value(&packet).expect("packet serializes");
        non_string_ref["structuralVerdict"][0]["evidence"]["computedInvariantRefs"] = json!([123]);
        let checks = validate_measurement_packet_value_v1(&non_string_ref);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-structural-verdict-new-shape"
                && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_packet_rejects_unknown_duplicate_and_dangling_fields() {
        let mut raw = serde_json::to_value(packet_fixture()).expect("packet serializes");
        raw["unexpected"] = json!(true);
        raw["computedInvariants"] = json!([
            {
                "invariantId": "duplicate:invariant",
                "kind": "measurement-invariant",
                "evaluator": "ag.foundation",
                "value": 0,
                "representation": {}
            },
            {
                "invariantId": "duplicate:invariant",
                "kind": "measurement-invariant",
                "evaluator": "ag.foundation",
                "value": 0,
                "representation": {}
            }
        ]);
        raw["computedInvariants"][0]["forgedField"] = json!(true);
        raw["analyticReadings"][0]["regime"] = json!("candidate-preview");
        raw["analyticReadings"][0]["claimStatus"] = json!("candidate");
        raw["analyticReadings"][0]["structuralVerdictRef"] = json!("structuralVerdict/missing");
        raw["suppliedData"][1]["suppliedId"] = json!("supplied:archmap");
        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields" && check.result == "fail"
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields"
                && check.examples.iter().any(|example| {
                    example.source.as_deref() == Some("computedInvariants[0].forgedField")
                })
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-computed-invariants-typed"
                && check.result == "fail"
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-supplied-data-ledger"
                && check.result == "fail"
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));
        raw["analyticReadings"][0]["regime"] = json!("certified");
        raw["analyticReadings"][0]["claimStatus"] = json!("certified");
        raw["analyticReadings"][0]["structuralVerdictRef"] = json!("structuralVerdict/missing");
        let certified_checks = validate_measurement_packet_value_v1(&raw);
        assert!(certified_checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));

        let mut nested_unknown = serde_json::to_value(packet_fixture()).expect("packet serializes");
        nested_unknown["computedInvariants"] = json!([{
            "invariantId": "saga-comparison:h1-transfer",
            "kind": "h1-comparison-transfer",
            "evaluator": "ag.saga-comparison",
            "status": "not_computed",
            "value": {"status": "not_computed"},
            "representation": {"basis": "test"},
            "contract": {
                "incidenceBridgeKind": "explicit",
                "h1ComparisonDataKind": "explicit",
                "normalizedComplexFingerprint": "fingerprint",
                "classPrerequisite": false,
                "targetClassComputed": false,
                "contractChecked": false,
                "forgedField": true
            }
        }]);
        let nested_checks = validate_measurement_packet_value_v1(&nested_unknown);
        assert!(nested_checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields"
                && check.examples.iter().any(|example| {
                    example.source.as_deref() == Some("computedInvariants[0].contract.forgedField")
                })
        }));

        let mut non_object_contract = nested_unknown.clone();
        non_object_contract["computedInvariants"][0]["contract"] = json!("forged");
        let non_object_checks = validate_measurement_packet_value_v1(&non_object_contract);
        assert!(non_object_checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields"
                && check.examples.iter().any(|example| {
                    example.source.as_deref() == Some("computedInvariants[0].contract")
                })
        }));

        let mut foreign_contract = nested_unknown;
        foreign_contract["computedInvariants"][0]["evaluator"] = json!("ag.foundation");
        let foreign_checks = validate_measurement_packet_value_v1(&foreign_contract);
        assert!(foreign_checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields"
                && check.examples.iter().any(|example| {
                    example.source.as_deref() == Some("computedInvariants[0].contract")
                })
        }));

        let mut wrong_contract_type =
            serde_json::to_value(packet_fixture()).expect("packet serializes");
        wrong_contract_type["computedInvariants"] = json!([{
            "invariantId": "saga-comparison:h1-transfer",
            "kind": "h1-comparison-transfer",
            "evaluator": "ag.saga-comparison",
            "status": "not_computed",
            "value": {"status": "not_computed"},
            "representation": {"basis": "test"},
            "contract": {
                "incidenceBridgeKind": "explicit",
                "h1ComparisonDataKind": "explicit",
                "normalizedComplexFingerprint": "fingerprint",
                "classPrerequisite": "false",
                "targetClassComputed": false,
                "contractChecked": false
            }
        }]);
        let wrong_type_checks = validate_measurement_packet_value_v1(&wrong_contract_type);
        assert!(wrong_type_checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields"
                && check.examples.iter().any(|example| {
                    example.source.as_deref() == Some("computedInvariants[0].contract")
                        && example.target.as_deref() == Some("classPrerequisite")
                })
        }));

        let mut missing_contract =
            serde_json::to_value(packet_fixture()).expect("packet serializes");
        missing_contract["computedInvariants"] = json!([{
            "invariantId": "saga-comparison:h1-transfer",
            "kind": "h1-comparison-transfer",
            "evaluator": "ag.saga-comparison",
            "status": "not_computed",
            "value": {"status": "not_computed"},
            "representation": {"basis": "test"}
        }]);
        let missing_contract_checks = validate_measurement_packet_value_v1(&missing_contract);
        assert!(missing_contract_checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields"
                && check.examples.iter().any(|example| {
                    example.source.as_deref() == Some("computedInvariants[0].contract")
                        && example.target.as_deref() == Some("contract")
                })
        }));
    }

    #[test]
    fn supplied_candidate_reading_with_structural_ref_fails_raw_validation() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["analyticReadings"][0]["claimStatus"] = json!("candidate");
        raw["analyticReadings"][0]["structuralVerdictRef"] = json!("/structuralVerdict/0");

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_measured_nonzero_class_ref_must_resolve_without_rewrite() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["structuralVerdict"][0]["verdict"] = json!("measured_nonzero");
        raw["structuralVerdict"][0]["verdictData"]["inScope"] = json!(true);
        raw["structuralVerdict"][0]["verdictData"]["zero"] = json!(false);
        raw["structuralVerdict"][0]["verdictData"]["nonZero"] = json!(true);
        raw["structuralVerdict"][0]["target"]["scopeSize"] =
            json!({"contexts": 1, "edges": 1, "triangles": 0});
        raw["structuralVerdict"][0]["target"]["classRef"] = json!("computedInvariants/missing");
        raw["structuralVerdict"][0]["evidence"]["computedInvariantRefs"] =
            json!(["invariant:actual"]);
        raw["computedInvariants"] = json!([{
            "invariantId": "invariant:actual",
            "kind": "measurement-invariant",
            "evaluator": "ag.cech-obstruction",
            "value": 1,
            "representation": {"source": "test"}
        }]);

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-structural-verdict-new-shape"
                && check.result == "fail"
                && check
                    .examples
                    .iter()
                    .any(|example| example.target.as_deref() == Some("computedInvariants/missing"))
        }));
    }

    #[test]
    fn supplied_computed_invariant_empty_object_fails_raw_validation() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["computedInvariants"] = json!([{}]);

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-computed-invariants-typed"
                && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_assumption_without_authored_id_fails_raw_validation() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["assumptions"][0]
            .as_object_mut()
            .unwrap()
            .remove("assumptionId");

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-assumption-ledger"
                && check.result == "fail"
                && check
                    .examples
                    .iter()
                    .any(|example| example.target.as_deref() == Some("assumptionId"))
        }));
    }

    #[test]
    fn supplied_laplacian_reading_must_be_marked_proxy() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["analyticReadings"][0]["evaluator"] = json!("ag.sheaf-laplacian");
        raw["analyticReadings"][0]["value"] = json!({
            "readingKind": "graph-laplacian-hodge-proxy@1"
        });
        raw["analyticReadings"][0]["regime"] = json!("analytic-measurement");
        raw["analyticReadings"][0]["claimStatus"] = json!("certified");
        raw["analyticReadings"][0]["fidelity"] = json!("faithful");

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
                && check
                    .examples
                    .iter()
                    .any(|example| example.target.as_deref() == Some("faithful"))
        }));
    }

    #[test]
    fn unresolved_assumption_dependency_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].depends_on_assumptions = vec!["missing/theorem".to_string()];
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-assumption-ledger" && check.result == "fail"
        }));
    }

    #[test]
    fn structural_verdict_dependency_field_is_serde_backward_compatible() {
        let packet = packet_fixture();
        assert!(
            packet.structural_verdict[0]
                .depends_on_assumptions
                .is_empty()
        );

        let serialized = serde_json::to_value(&packet).expect("packet serializes");
        assert!(
            serialized["structuralVerdict"][0]
                .get("dependsOnAssumptions")
                .is_none(),
            "empty dependsOnAssumptions stays additive and omitted from legacy-shaped rows"
        );
    }

    #[test]
    fn assumption_dependency_propagation_only_updates_dependent_measured_rows() {
        let mut packet = packet_fixture();
        let finite_site_assumption = assumption_id_for_schema(&packet.assumptions[0]);
        packet.structural_verdict[0].verdict = "measured_zero".to_string();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].depends_on_assumptions = vec![finite_site_assumption.clone()];
        let square_free_assumption = AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/5.1".to_string(),
            assumption: "square-free witness variables selected by supplied law-equation-surface"
                .to_string(),
            status: "checked".to_string(),
            checked_by: Some("test".to_string()),
            assumed_by: None,
        };
        let square_free_assumption_id = assumption_id_for_schema(&square_free_assumption);
        packet.structural_verdict.push(AgStructuralVerdictV1 {
            evaluator: "ag.square-free-repair".to_string(),
            law: "ag.square-free-repair".to_string(),
            verdict: "measured_zero".to_string(),
            verdict_data: AgVerdictDataV1 {
                in_scope: true,
                zero: true,
                non_zero: false,
                method_status: "square_free_ideal_computed".to_string(),
                cert_ref: None,
            },
            depends_on_assumptions: vec![square_free_assumption_id],
            reason: Some("independent square-free row remains measured zero".to_string()),
        });
        packet.assumptions[0].status = "violated".to_string();
        packet.assumptions[0].checked_by = None;
        packet.assumptions.push(square_free_assumption);

        apply_assumption_dependency_propagation(&mut packet);

        assert_eq!(packet.structural_verdict[0].verdict, "not_computed");
        assert_eq!(
            packet.structural_verdict[0].verdict_data.method_status,
            "depends_on_violated_assumption"
        );
        let expected_reason = format!("depends_on violated {finite_site_assumption}");
        assert_eq!(
            packet.structural_verdict[0].reason.as_deref(),
            Some(expected_reason.as_str())
        );
        assert_eq!(packet.structural_verdict[1].verdict, "measured_zero");
        assert!(packet.structural_verdict[1].verdict_data.zero);
    }

    #[test]
    fn theorem_candidate_reading_cannot_link_structural_verdict() {
        let mut packet = packet_fixture();
        packet.analytic_readings[0].structural_verdict_ref =
            Some("/structuralVerdict/0".to_string());
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));
    }

    #[test]
    fn boundary_statements_reproduce_non_conclusion_compat_text() {
        let packet = packet_fixture();
        let checks = validate_measurement_packet_v1(&packet);

        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "pass"
        }));
        assert!(packet.non_conclusions.iter().all(|text| {
            packet
                .boundary_statements
                .iter()
                .any(|statement| statement.text == *text)
        }));
        assert!(packet.boundary_statements.iter().any(|statement| {
            statement.kind == "unmeasured_support"
                && statement
                    .scope_refs
                    .iter()
                    .any(|scope_ref| scope_ref.starts_with("structuralVerdict/"))
        }));
        assert!(packet.boundary_statements.iter().any(|statement| {
            statement.kind == "not_applicable"
                && statement
                    .scope_refs
                    .iter()
                    .any(|scope_ref| scope_ref == "candidate:test")
        }));
    }

    #[test]
    fn boundary_statement_empty_scope_refs_fail_validation() {
        let mut packet = packet_fixture();
        packet.boundary_statements[0].scope_refs.clear();
        let checks = validate_measurement_packet_v1(&packet);

        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn boundary_statement_unresolved_scope_refs_fail_validation() {
        let mut packet = packet_fixture();
        packet.boundary_statements[0].scope_refs = vec!["missing:scope".to_string()];
        let checks = validate_measurement_packet_v1(&packet);

        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn comparison_silence_requires_next_input_and_typed_boundary() {
        let mut packet = packet_fixture();
        packet.computed_invariants.push(json!({
            "invariantId": "saga-comparison:h1-transfer",
            "kind": "h1-comparison-transfer",
            "evaluator": "ag.saga-comparison",
            "status": "silence_by_design",
            "whatNext": "supply the missing comparison input",
            "value": {"status": "silence_by_design"},
            "representation": {"basis": "typed-silence"},
            "contract": {
                "incidenceBridgeKind": "unknown",
                "h1ComparisonDataKind": "unknown",
                "normalizedComplexFingerprint": "unknown",
                "classPrerequisite": false,
                "targetClassComputed": false,
                "contractChecked": false
            }
        }));
        packet.boundary_statements.push(BoundaryStatementV1 {
            id: "boundary:saga-comparison".to_string(),
            kind: "silence_by_design".to_string(),
            scope_refs: vec!["saga-comparison:h1-transfer".to_string()],
            reason: "comparison_data_not_supplied".to_string(),
            text: "supply the missing comparison input".to_string(),
        });
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "pass"
        }));

        let mut missing_what_next = packet.clone();
        missing_what_next.computed_invariants[0]
            .as_object_mut()
            .unwrap()
            .remove("whatNext");
        let checks = validate_measurement_packet_v1(&missing_what_next);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));

        let mut missing_boundary = packet.clone();
        missing_boundary.boundary_statements.pop();
        let checks = validate_measurement_packet_v1(&missing_boundary);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));

        let mut mismatched_boundary = packet;
        mismatched_boundary
            .boundary_statements
            .last_mut()
            .unwrap()
            .text = "different guidance".to_string();
        let checks = validate_measurement_packet_v1(&mismatched_boundary);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn comparison_contract_kind_owner_cannot_be_bypassed() {
        let mut packet = packet_fixture();
        packet.computed_invariants.push(json!({
            "invariantId": "comparison-owner-bypass",
            "kind": "h1-comparison-transfer",
            "evaluator": "ag.foundation",
            "status": "silence_by_design",
            "whatNext": "supply the missing comparison input",
            "value": {"status": "silence_by_design"},
            "representation": {"basis": "typed-silence"}
        }));
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields" && check.result == "fail"
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-computed-invariants-typed"
                && check.result == "fail"
        }));
    }

    #[test]
    fn comparison_contract_status_flags_must_match_output_status() {
        let mut packet = packet_fixture();
        packet.computed_invariants.push(json!({
            "invariantId": "comparison-established-without-conclusion",
            "kind": "h1-comparison-transfer",
            "evaluator": "ag.saga-comparison",
            "status": "established",
            "value": {"status": "established"},
            "representation": {"basis": "typed-comparison"},
            "contract": {
                "incidenceBridgeKind": "explicit",
                "h1ComparisonDataKind": "explicit",
                "normalizedComplexFingerprint": "fingerprint",
                "classPrerequisite": true,
                "targetClassComputed": true,
                "contractChecked": true
            }
        }));
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields"
                && check.result == "fail"
                && check.examples.iter().any(|example| {
                    example.source.as_deref() == Some("computedInvariants[0].contract")
                })
        }));

        let mut missing_failure = packet_fixture();
        missing_failure.computed_invariants.push(json!({
            "invariantId": "comparison-contract-failure-without-code",
            "kind": "h1-comparison-transfer",
            "evaluator": "ag.saga-comparison",
            "status": "not_computed",
            "value": {"status": "not_computed"},
            "representation": {"basis": "typed-comparison"},
            "contract": {
                "incidenceBridgeKind": "explicit",
                "h1ComparisonDataKind": "explicit",
                "normalizedComplexFingerprint": "fingerprint",
                "classPrerequisite": true,
                "targetClassComputed": true,
                "contractChecked": false
            }
        }));
        let checks = validate_measurement_packet_v1(&missing_failure);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields"
                && check.result == "fail"
                && check.examples.iter().any(|example| {
                    example.source.as_deref() == Some("computedInvariants[0].contract")
                })
        }));

        let mut missing_status = packet_fixture();
        missing_status.computed_invariants.push(json!({
            "invariantId": "what-next-without-status",
            "kind": "measurement-invariant",
            "evaluator": "ag.foundation",
            "value": {},
            "representation": {},
            "whatNext": "supply missing input"
        }));
        let checks = validate_measurement_packet_v1(&missing_status);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn boundary_statement_unknown_kind_fails_validation() {
        let mut packet = packet_fixture();
        packet.boundary_statements[0].kind = "maybe_conclusion".to_string();
        let checks = validate_measurement_packet_v1(&packet);

        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn violated_assumption_boundary_scopes_to_not_computed_verdict() {
        let mut packet = packet_fixture();
        let finite_site_assumption = assumption_id_for_schema(&packet.assumptions[0]);
        packet.structural_verdict[0].verdict = "not_computed".to_string();
        packet.structural_verdict[0].verdict_data.method_status =
            "empty_selected_scope".to_string();
        packet.structural_verdict[0].depends_on_assumptions = vec![finite_site_assumption.clone()];
        packet.assumptions[0].status = "violated".to_string();
        packet.assumptions[0].checked_by = None;
        packet.boundary_statements = boundary_statements_for_measurement_packet(&packet);

        assert!(packet.boundary_statements.iter().any(|statement| {
            statement.kind == "violated_assumption"
                && statement
                    .scope_refs
                    .iter()
                    .any(|scope_ref| scope_ref == &finite_site_assumption)
                && statement
                    .scope_refs
                    .iter()
                    .any(|scope_ref| scope_ref.starts_with("structuralVerdict/"))
        }));
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "pass"
        }));

        let mut broken = packet;
        let statement = broken
            .boundary_statements
            .iter_mut()
            .find(|statement| statement.kind == "violated_assumption")
            .expect("violated assumption boundary exists");
        statement.scope_refs = vec!["part8/4.2".to_string()];
        let checks = validate_measurement_packet_v1(&broken);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn cech_empty_selected_cover_contexts_are_not_computed() {
        let mut normalized = normalized_fixture();
        normalized.covers[0].context_ids.clear();
        let profile = packet_fixture().profile;

        let measurement = evaluate_cech_obstruction_v1(&normalized, &profile, None);

        assert_eq!(measurement.verdict, "not_computed");
        assert!(!measurement.zero);
        assert!(!measurement.non_zero);
        assert_eq!(measurement.method_status, "empty_selected_scope");
        assert!(measurement.reason.contains("empty_selected_scope"));
        assert!(measurement.assumptions.iter().any(|entry| {
            entry.theorem_ref == "part8/B.8.2-empty-selected-scope"
                && entry.status == "violated"
                && entry.assumption == "U-adequate cover selects a non-empty Cech 1-skeleton"
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
    fn gluing_projection_caps_cocycle_support_edges_and_reports_omissions() {
        let mut normalized = normalized_fixture();
        let mut context_ids = Vec::new();
        let mut contexts = Vec::new();
        let mut atoms = Vec::new();
        for index in 0..=GLUING_COCYCLE_EDGE_RENDER_LIMIT + 1 {
            let context = format!("ctx:{index}");
            let atom_id = format!("atom:section-value:{index}");
            context_ids.push(context.clone());
            contexts.push(NormalizedContextV2 {
                source_context_id: context.clone(),
                normalized_context_id: context.clone(),
                atom_ids: vec![atom_id.clone()],
                restricts_to: if index <= GLUING_COCYCLE_EDGE_RENDER_LIMIT {
                    vec![format!("ctx:{}", index + 1)]
                } else {
                    Vec::new()
                },
                source_refs: vec![format!("fixture://{context}")],
                poset_status: "selected".to_string(),
            });
            atoms.push(NormalizedAtomV2 {
                source_atom_id: atom_id.clone(),
                normalized_atom_id: atom_id,
                atom_kind: "component".to_string(),
                subject: context.clone(),
                axis: "cech".to_string(),
                predicate: "sectionValue".to_string(),
                object: Some(format!("section:{index}")),
                source_refs: vec![format!("fixture://{context}")],
                context_memberships: vec![context],
                normalization_status: "normalized".to_string(),
            });
        }
        normalized.contexts = contexts;
        normalized.atoms = atoms;
        normalized.covers[0].context_ids = context_ids;
        normalized.summary.atom_count = normalized.atoms.len();
        normalized.summary.normalized_atom_count = normalized.atoms.len();
        normalized.summary.context_count = normalized.contexts.len();

        let packet = packet_fixture();
        let gluing = gluing_geometry_projection_v1(&normalized, &packet);

        assert_eq!(
            gluing["cocycleRibbon"]["supportEdges"]
                .as_array()
                .expect("support edges are array")
                .len(),
            GLUING_COCYCLE_EDGE_RENDER_LIMIT,
            "cocycle ribbon support must be capped before entering the viewer projection"
        );
        assert_eq!(
            gluing["renderLimits"]["cocycleSupportEdges"].as_u64(),
            Some(GLUING_COCYCLE_EDGE_RENDER_LIMIT as u64)
        );
        assert_eq!(
            gluing["omittedGeometryCounts"]["cocycleSupportEdges"].as_u64(),
            Some(1),
            "cocycle ribbon omissions must be reported for large H1 support"
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
                        "support": ["x_checkout", "x_inventory"],
                        "supportAtomRefs": ["atom:checkout-inventory"]
                    },
                    {
                        "generatorId": "g1",
                        "support": ["x_inventory", "x_payment"],
                        "supportAtomRefs": ["atom:inventory-payment"]
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
