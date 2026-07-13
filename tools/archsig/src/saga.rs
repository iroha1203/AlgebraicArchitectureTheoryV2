use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};

use crate::repair_plan::comparison_complex_fingerprint;
use crate::{
    ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION, ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS,
    ARCHSIG_SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA, AgAssumptionLedgerEntryV1,
    AgStructuralVerdictV1, AgVerdictDataV1, ArchMapDocumentV2, RepairPlanDocumentV1,
    assumption_id_for_schema,
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
    let sheaf_assumption =
        plan.true_sheaf_certificate
            .as_ref()
            .and_then(Value::as_object)
            .and_then(|certificate| {
                (certificate.get("globalCondition").and_then(Value::as_str) == Some("assumed"))
                    .then(|| AgAssumptionLedgerEntryV1 {
                        theorem_ref: "part4/4.7".to_string(),
                        assumption: format!("global sheaf condition for {}", plan.id),
                        status: "assumed".to_string(),
                        checked_by: None,
                        assumed_by: Some("trueSheafCertificate author".to_string()),
                    })
            });
    let faithfulness_assumption =
        (plan.faithfulness.mode == "supplied").then(|| AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/4.6".to_string(),
            assumption: format!("faithfulness law supplied for {}", plan.id),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some("RepairPlan author".to_string()),
        });
    let mut evaluator_assumption_ids = vec![enumeration_assumption_id.clone()];
    if let Some(assumption) = faithfulness_assumption.as_ref() {
        evaluator_assumption_ids.push(assumption_id_for_schema(assumption));
    }
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
        depends_on_assumptions: evaluator_assumption_ids.clone(),
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
            depends_on_assumptions: evaluator_assumption_ids.clone(),
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
            depends_on_assumptions: evaluator_assumption_ids.clone(),
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
            depends_on_assumptions: evaluator_assumption_ids.clone(),
            reason: Some(if boundary.in_b1 {
                "residual is covered, but semantic projection is not faithful for the selected RepairPlan complex".to_string()
            } else {
                "global coherence is blocked because the supplied residual is not a B1 boundary".to_string()
            }),
        });
    }

    let mut computed_invariants = vec![
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
                "basis": if plan.faithfulness.mode == "supplied" { "supplied-data" } else { "complete-support" },
                "completeSupportPrimitiveCount": plan.primitives.iter().filter(|primitive| primitive.support.kind == "complete").count()
            }
        }),
    ];
    if class_supply_is_checked(archmap, plan) {
        let class_nonzero = !boundary.in_b1;
        structural_verdict.push(AgStructuralVerdictV1 {
            evaluator: "ag.saga-descent".to_string(),
            law: "saga.residual-class".to_string(),
            verdict: if class_nonzero { "measured_nonzero" } else { "measured_zero" }
                .to_string(),
            verdict_data: AgVerdictDataV1 {
                in_scope: true,
                zero: !class_nonzero,
                non_zero: class_nonzero,
                method_status: if class_nonzero {
                    "nonzero_class_representative"
                } else {
                    "zero_class_representative"
                }
                .to_string(),
                cert_ref: Some("computedInvariants/saga-descent:residual-class".to_string()),
            },
            depends_on_assumptions: evaluator_assumption_ids.clone(),
            reason: Some(if class_nonzero {
                format!("{ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS}: supplied Z1 representative is not in B1")
            } else {
                "supplied Z1 representative is zero in Z1/B1".to_string()
            }),
        });
        computed_invariants.push(json!({
            "invariantId": "saga-descent:residual-class",
            "evaluator": "ag.saga-descent",
            "residualClassSupport": {
                "basis": "Z1/B1",
                "representative": boundary.residual_support,
                "nonZero": class_nonzero,
                "quotient": "Z1/B1",
                "cocycle": {
                    "checked": true,
                    "deltaOne": "zero",
                    "tripleOverlapRefs": plan.complex.triple_overlaps.iter().map(|triple| json!({
                        "tripleRef": triple.id,
                        "overlapRefs": triple.overlap_refs
                    })).collect::<Vec<_>>()
                }
            },
            "suppliedSlots": [
                "complex.tripleOverlaps",
                "coefficient",
                "trueSheafCertificate",
                "gluingData"
            ]
        }));
    }
    computed_invariants.push(evaluate_saga_comparison_v1(plan, &structural_verdict));
    let mut assumptions = vec![enumeration_assumption];
    if let Some(sheaf_assumption) = sheaf_assumption {
        assumptions.push(sheaf_assumption);
    }
    if let Some(faithfulness_assumption) = faithfulness_assumption {
        assumptions.push(faithfulness_assumption);
    }
    SagaDescentMeasurementV1 {
        structural_verdict,
        computed_invariants,
        assumptions,
    }
}

fn evaluate_saga_comparison_v1(
    plan: &RepairPlanDocumentV1,
    structural_verdict: &[AgStructuralVerdictV1],
) -> Value {
    let Some(comparison) = plan.comparison.as_ref() else {
        return json!({
            "invariantId": "saga-comparison:h1-transfer",
            "evaluator": "ag.saga-comparison",
            "kind": "h1-comparison-transfer",
            "status": "silence_by_design",
            "reason": "comparison_data_not_supplied"
        });
    };
    let class_available = structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.saga-descent"
            && verdict.law == "saga.residual-class"
            && matches!(
                verdict.verdict.as_str(),
                "measured_zero" | "measured_nonzero"
            )
    });
    let class_nonzero = structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.saga-descent"
            && verdict.law == "saga.residual-class"
            && verdict.verdict == "measured_nonzero"
    });
    let bridge_kind = comparison["incidenceBridge"]["kind"]
        .as_str()
        .unwrap_or("unknown");
    let h1_kind = comparison["h1ComparisonData"]["kind"]
        .as_str()
        .unwrap_or("unknown");
    let established = class_available;
    json!({
        "invariantId": "saga-comparison:h1-transfer",
        "evaluator": "ag.saga-comparison",
        "kind": "h1-comparison-transfer",
        "status": if established { "established" } else { "not_computed" },
        "conclusionCode": established.then_some(ARCHSIG_SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA),
        "contract": {
            "incidenceBridgeKind": bridge_kind,
            "h1ComparisonDataKind": h1_kind,
            "normalizedComplexFingerprint": comparison_complex_fingerprint(plan),
            "classPrerequisite": class_available
        },
        "suppliedCochainMap": {
            "level": "cochain",
            "kind": h1_kind,
            "contractChecked": true
        },
        "generatedQuotientTransfer": if established {
            json!({
                "level": "quotient",
                "kind": "Z1/B1-class-transfer",
                "preservesZeroPredicate": true,
                "sourceClassNonZero": class_nonzero,
                "targetClassNonZero": class_nonzero,
                "sourceInvariant": "saga-descent:residual-class",
                "targetInvariant": "saga-comparison:h1-transfer"
            })
        } else {
            Value::Null
        },
        "failureCode": if established { Value::Null } else { json!(ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION) },
        "nonConclusions": [
            "Supplied cochain data and generated quotient-level transfer are separate structures.",
            "The transfer reading is relative to the supplied finite comparison contract."
        ]
    })
}

fn class_supply_is_checked(archmap: &ArchMapDocumentV2, plan: &RepairPlanDocumentV1) -> bool {
    let overlap_ids = plan
        .complex
        .overlaps
        .iter()
        .map(|overlap| overlap.id.as_str())
        .collect::<BTreeSet<_>>();
    let triple_ok = !plan.complex.triple_overlaps.is_empty()
        && plan.complex.triple_overlaps.iter().all(|triple| {
            let refs = triple.overlap_refs.iter().collect::<BTreeSet<_>>();
            triple.overlap_refs.len() == 3
                && refs.len() == 3
                && refs
                    .iter()
                    .all(|overlap| overlap_ids.contains(overlap.as_str()))
                && triple_cocycle_is_zero(plan, &triple.overlap_refs)
        });
    let coefficient_ok = plan.coefficient.is_f2_additive()
        || plan.coefficient.supplied().is_some_and(|coefficient| {
            coefficient.kind == "f2-additive"
                && coefficient.characteristic == 2
                && coefficient.additive
                && coefficient.delta_one_after_delta_zero
                && coefficient.zero_maps_to_zero
        });
    let certificate_ok = plan
        .true_sheaf_certificate
        .as_ref()
        .and_then(Value::as_object)
        .is_some_and(|certificate| {
            certificate.get("kind").and_then(Value::as_str) == Some("true-sheaf-certificate")
                && certificate
                    .get("globalCondition")
                    .and_then(Value::as_str)
                    .is_some_and(|condition| matches!(condition, "assumed"))
                && certificate
                    .get("coverRef")
                    .and_then(Value::as_str)
                    .is_some_and(|cover| archmap.covers.iter().any(|item| item.id == cover))
                && certificate
                    .get("memberCharts")
                    .and_then(Value::as_array)
                    .is_some_and(|members| {
                        !members.is_empty()
                            && members.iter().all(|member| {
                                member.as_str().is_some_and(|chart| {
                                    plan.complex.charts.iter().any(|item| item == chart)
                                })
                            })
                            && members
                                .iter()
                                .filter_map(Value::as_str)
                                .collect::<BTreeSet<_>>()
                                .len()
                                == members.len()
                    })
        });
    let gluing_ok = plan
        .gluing_data
        .as_ref()
        .and_then(Value::as_object)
        .is_some_and(|gluing| {
            gluing.get("kind").and_then(Value::as_str) == Some("gluing-data")
                && gluing
                    .get("overlapRefs")
                    .and_then(Value::as_array)
                    .is_some_and(|refs| {
                        refs.len() == overlap_ids.len()
                            && refs
                                .iter()
                                .filter_map(Value::as_str)
                                .collect::<BTreeSet<_>>()
                                == overlap_ids
                    })
                && gluing
                    .get("sectionRefs")
                    .and_then(Value::as_array)
                    .is_some_and(|refs| {
                        let overlaps = refs
                            .iter()
                            .filter_map(Value::as_object)
                            .filter_map(|item| item.get("overlapRef")?.as_str())
                            .collect::<BTreeSet<_>>();
                        let sections = refs
                            .iter()
                            .filter_map(Value::as_object)
                            .filter_map(|item| item.get("sectionRef")?.as_str())
                            .filter(|section| !section.is_empty())
                            .collect::<BTreeSet<_>>();
                        refs.len() == overlap_ids.len()
                            && overlaps == overlap_ids
                            && sections.len() == overlap_ids.len()
                    })
        });
    triple_ok && coefficient_ok && certificate_ok && gluing_ok
}

fn triple_cocycle_is_zero(plan: &RepairPlanDocumentV1, overlap_refs: &[String]) -> bool {
    let primitives = plan
        .primitives
        .iter()
        .map(|primitive| (primitive.overlap_ref.as_str(), primitive))
        .collect::<BTreeMap<_, _>>();
    let mut parity = BTreeMap::<&str, usize>::new();
    for overlap_ref in overlap_refs {
        let Some(primitive) = primitives.get(overlap_ref.as_str()) else {
            return false;
        };
        for variable in &primitive.support.variables {
            *parity.entry(variable.as_str()).or_default() += 1;
        }
    }
    parity.values().all(|count| count % 2 == 0)
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
