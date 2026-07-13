use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};

use crate::{
    AgAssumptionLedgerEntryV1, AgStructuralVerdictV1, AgVerdictDataV1, ArchMapDocumentV2,
    RepairPlanDocumentV1, assumption_id_for_schema,
};

#[derive(Debug, Clone)]
pub(crate) struct SagaDescentMeasurementV1 {
    pub structural_verdict: Vec<AgStructuralVerdictV1>,
    pub computed_invariants: Vec<Value>,
    pub assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

pub(crate) fn evaluate_saga_descent_v1(
    archmap: &ArchMapDocumentV2,
    plan: &RepairPlanDocumentV1,
) -> SagaDescentMeasurementV1 {
    let boundary = solve_boundary_membership(plan);
    let closure = closure_diagnostics(archmap, plan);
    let enumeration_assumption = AgAssumptionLedgerEntryV1 {
        theorem_ref: "part10/repair-plan-enumeration".to_string(),
        assumption: format!(
            "repair-plan complex enumeration completeness for {}",
            plan.id
        ),
        status: "assumed".to_string(),
        checked_by: None,
        assumed_by: Some("repair-plan author".to_string()),
    };
    let enumeration_assumption_id = assumption_id_for_schema(&enumeration_assumption);
    let mut structural_verdict = Vec::new();
    let boundary_verdict = if boundary.in_b1 {
        "measured_zero"
    } else {
        "measured_nonzero"
    };
    structural_verdict.push(AgStructuralVerdictV1 {
        evaluator: "ag.saga-descent".to_string(),
        law: "saga.residual-boundary-membership".to_string(),
        verdict: boundary_verdict.to_string(),
        verdict_data: AgVerdictDataV1 {
            in_scope: true,
            zero: boundary.in_b1,
            non_zero: !boundary.in_b1,
            method_status: if boundary.in_b1 {
                "residual_in_b1"
            } else {
                "residual_not_in_b1"
            }
            .to_string(),
            cert_ref: Some("computedInvariants/saga-descent:boundary-membership".to_string()),
        },
        depends_on_assumptions: vec![enumeration_assumption_id.clone()],
        reason: Some(if boundary.in_b1 {
            "supplied residual lies in B1 for the selected RepairPlan complex".to_string()
        } else {
            "supplied residual is not in B1 for the selected RepairPlan complex".to_string()
        }),
    });

    if plan.faithfulness.mode == "none" {
        structural_verdict.push(AgStructuralVerdictV1 {
            evaluator: "ag.saga-descent".to_string(),
            law: "saga.global-coherence".to_string(),
            verdict: "unmeasured".to_string(),
            verdict_data: AgVerdictDataV1 {
                in_scope: true,
                zero: false,
                non_zero: false,
                method_status: "complete_support_not_declared".to_string(),
                cert_ref: None,
            },
            depends_on_assumptions: Vec::new(),
            reason: Some(
                "complete-support declaration or Stage 2 faithfulness data is required before global coherence can be stated".to_string(),
            ),
        });
    } else if boundary.in_b1
        && closure.residual_component_covered
        && closure.residual_component_faithful
    {
        structural_verdict.push(AgStructuralVerdictV1 {
            evaluator: "ag.saga-descent".to_string(),
            law: "saga.global-coherence".to_string(),
            verdict: "measured_zero".to_string(),
            verdict_data: AgVerdictDataV1 {
                in_scope: true,
                zero: true,
                non_zero: false,
                method_status: "complete_support_global_coherent".to_string(),
                cert_ref: Some("computedInvariants/saga-descent:closure-diagnostics".to_string()),
            },
            depends_on_assumptions: vec![enumeration_assumption_id.clone()],
            reason: Some(
                "residual is a B1 boundary inside the complete-support RepairPlan regime"
                    .to_string(),
            ),
        });
    } else if boundary.in_b1 && !closure.residual_component_covered {
        structural_verdict.push(AgStructuralVerdictV1 {
            evaluator: "ag.saga-descent".to_string(),
            law: "saga.global-coherence".to_string(),
            verdict: "unmeasured".to_string(),
            verdict_data: AgVerdictDataV1 {
                in_scope: true,
                zero: false,
                non_zero: false,
                method_status: "residual_not_covered".to_string(),
                cert_ref: Some("computedInvariants/saga-descent:closure-diagnostics".to_string()),
            },
            depends_on_assumptions: vec![enumeration_assumption_id.clone()],
            reason: Some(
                "residual is a B1 boundary, but semantic projection does not cover every residual component for the selected RepairPlan complex".to_string(),
            ),
        });
    } else {
        structural_verdict.push(AgStructuralVerdictV1 {
            evaluator: "ag.saga-descent".to_string(),
            law: "saga.global-coherence".to_string(),
            verdict: "measured_nonzero".to_string(),
            verdict_data: AgVerdictDataV1 {
                in_scope: true,
                zero: false,
                non_zero: true,
                method_status: if boundary.in_b1 {
                    "alias_not_faithful"
                } else {
                    "residual_not_in_b1"
                }
                .to_string(),
                cert_ref: Some("computedInvariants/saga-descent:closure-diagnostics".to_string()),
            },
            depends_on_assumptions: vec![enumeration_assumption_id.clone()],
            reason: Some(if boundary.in_b1 {
                "residual is covered, but semantic projection is not faithful for the selected RepairPlan complex".to_string()
            } else {
                "global coherence is blocked because the supplied residual is not a B1 boundary".to_string()
            }),
        });
    }

    let computed_invariants = vec![
        json!({
            "invariantId": "saga-descent:boundary-membership",
            "evaluator": "ag.saga-descent",
            "boundaryMembership": {
                "inB1": boundary.in_b1,
                "witnessPrimitiveCombination": boundary.witness_chart_assignment,
                "residualSupport": boundary.residual_support
            }
        }),
        json!({
            "invariantId": "saga-descent:closure-diagnostics",
            "evaluator": "ag.saga-descent",
            "closureDiagnostics": {
                "residualComponentCovered": closure.residual_component_covered,
                "residualComponentFaithful": closure.residual_component_faithful,
                "aliasWitnesses": closure.alias_witnesses
            },
            "faithfulnessBasis": {
                "mode": plan.faithfulness.mode,
                "completeSupportPrimitiveCount": plan.primitives.iter().filter(|primitive| primitive.support.kind == "complete").count()
            }
        }),
    ];
    SagaDescentMeasurementV1 {
        structural_verdict,
        computed_invariants,
        assumptions: vec![enumeration_assumption],
    }
}

#[derive(Debug, Clone)]
struct BoundaryMembershipResult {
    in_b1: bool,
    witness_chart_assignment: Vec<Value>,
    residual_support: Vec<Value>,
}

#[derive(Debug, Clone)]
struct ClosureDiagnostics {
    residual_component_covered: bool,
    residual_component_faithful: bool,
    alias_witnesses: Vec<Value>,
}

fn solve_boundary_membership(plan: &RepairPlanDocumentV1) -> BoundaryMembershipResult {
    let charts = plan.complex.charts.clone();
    let chart_index = charts
        .iter()
        .enumerate()
        .map(|(index, chart)| (chart.as_str(), index))
        .collect::<BTreeMap<_, _>>();
    let variables = residual_variables(plan);
    let variable_index = variables
        .iter()
        .enumerate()
        .map(|(index, variable)| (variable.as_str(), index))
        .collect::<BTreeMap<_, _>>();
    let unknown_count = charts.len() * variables.len();
    let mut rows = Vec::<Vec<u8>>::new();
    for overlap in &plan.complex.overlaps {
        let left_index = chart_index[overlap.left.as_str()];
        let right_index = chart_index[overlap.right.as_str()];
        let support = plan
            .primitives
            .iter()
            .find(|primitive| primitive.overlap_ref == overlap.id)
            .map(|primitive| {
                primitive
                    .support
                    .variables
                    .iter()
                    .map(String::as_str)
                    .collect::<BTreeSet<_>>()
            })
            .unwrap_or_default();
        for variable in &variables {
            let mut row = vec![0; unknown_count + 1];
            let variable_offset = variable_index[variable.as_str()];
            row[left_index * variables.len() + variable_offset] ^= 1;
            row[right_index * variables.len() + variable_offset] ^= 1;
            row[unknown_count] = u8::from(support.contains(variable.as_str()));
            rows.push(row);
        }
    }
    let solution = solve_f2(rows, unknown_count);
    BoundaryMembershipResult {
        in_b1: solution.is_some(),
        witness_chart_assignment: solution
            .map(|solution| chart_assignment_json(&charts, &variables, &solution))
            .unwrap_or_default(),
        residual_support: residual_support_json(plan),
    }
}

fn residual_variables(plan: &RepairPlanDocumentV1) -> Vec<String> {
    plan.primitives
        .iter()
        .flat_map(|primitive| primitive.support.variables.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn residual_support_json(plan: &RepairPlanDocumentV1) -> Vec<Value> {
    plan.primitives
        .iter()
        .map(|primitive| {
            json!({
                "overlapRef": primitive.overlap_ref,
                "support": primitive.support.variables
            })
        })
        .collect()
}

fn chart_assignment_json(charts: &[String], variables: &[String], solution: &[u8]) -> Vec<Value> {
    charts
        .iter()
        .enumerate()
        .map(|(chart_index, chart)| {
            let active = variables
                .iter()
                .enumerate()
                .filter_map(|(variable_index, variable)| {
                    (solution[chart_index * variables.len() + variable_index] == 1)
                        .then(|| variable.clone())
                })
                .collect::<Vec<_>>();
            json!({
                "chartRef": chart,
                "variables": active
            })
        })
        .collect()
}

fn solve_f2(mut rows: Vec<Vec<u8>>, unknown_count: usize) -> Option<Vec<u8>> {
    let mut pivot_row = 0;
    let mut pivots = Vec::<(usize, usize)>::new();
    for column in 0..unknown_count {
        let pivot = (pivot_row..rows.len()).find(|row| rows[*row][column] == 1);
        let Some(pivot) = pivot else {
            continue;
        };
        rows.swap(pivot_row, pivot);
        for row in 0..rows.len() {
            if row != pivot_row && rows[row][column] == 1 {
                for col in column..=unknown_count {
                    rows[row][col] ^= rows[pivot_row][col];
                }
            }
        }
        pivots.push((pivot_row, column));
        pivot_row += 1;
    }
    if rows
        .iter()
        .any(|row| row[..unknown_count].iter().all(|value| *value == 0) && row[unknown_count] == 1)
    {
        return None;
    }
    let mut solution = vec![0; unknown_count];
    for (row, column) in pivots {
        solution[column] = rows[row][unknown_count];
    }
    Some(solution)
}

fn closure_diagnostics(
    archmap: &ArchMapDocumentV2,
    plan: &RepairPlanDocumentV1,
) -> ClosureDiagnostics {
    let k = plan
        .semantic_projection
        .k
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let residual_variables = residual_variables(plan);
    let residual_variable_set = residual_variables
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let residual_component_covered = residual_variables
        .iter()
        .all(|variable| k.contains(variable.as_str()));
    let mut by_subject = BTreeMap::<&str, Vec<&str>>::new();
    for row in &plan.semantic_projection.pi {
        if !residual_variable_set.contains(row.subject.as_str()) {
            continue;
        }
        by_subject
            .entry(row.subject.as_str())
            .or_default()
            .push(row.atom_ref.as_str());
    }
    let atom_subjects = archmap
        .atoms
        .iter()
        .map(|atom| (atom.id.as_str(), atom.subject.as_str()))
        .collect::<BTreeMap<_, _>>();
    let alias_witnesses = by_subject
        .into_iter()
        .filter(|(_, atom_refs)| atom_refs.len() > 1)
        .map(|(subject, atom_refs)| {
            json!({
                "subject": subject,
                "atomRefs": atom_refs,
                "archmapSubjects": atom_refs.iter().filter_map(|atom_ref| atom_subjects.get(atom_ref).copied()).collect::<Vec<_>>()
            })
        })
        .collect::<Vec<_>>();
    ClosureDiagnostics {
        residual_component_covered,
        residual_component_faithful: alias_witnesses.is_empty(),
        alias_witnesses,
    }
}
