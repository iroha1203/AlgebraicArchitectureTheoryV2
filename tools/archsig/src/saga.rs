use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};

use crate::law_execution::LawExecutionPlanV1;
use crate::repair_plan::{
    comparison_complex_fingerprint, comparison_target_complex, complex_has_valid_finite_incidence,
    explicit_h1_comparison_checks, presentation_generated_h1_checks,
    presentation_generated_h1_output,
};
use crate::{
    ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION, ARCHSIG_DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS,
    ARCHSIG_MEASURED_LAW_DEFECT_AT_CHART, ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS,
    ARCHSIG_SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA,
    ARCHSIG_SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS, ARCHSIG_SAGA_CONCLUSIONS_V1_SCHEMA,
    AgAssumptionLedgerEntryV1, AgStructuralVerdictV1, AgVerdictDataV1, ArchMapDocumentV2,
    MeasurementProfileV1, NormalizedArchMapV2, RepairPlanComplexV1, RepairPlanDocumentV1,
    assumption_id_for_schema,
};

#[derive(Debug, Clone)]
pub(crate) struct SagaDescentMeasurementV1 {
    pub structural_verdict: Vec<AgStructuralVerdictV1>,
    pub computed_invariants: Vec<Value>,
    pub assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
pub(crate) struct SagaGroundedMeasurementV1 {
    pub structural_verdict: Vec<AgStructuralVerdictV1>,
    pub computed_invariants: Vec<Value>,
    pub assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

pub(crate) fn evaluate_saga_grounded_v1(
    archmap: &ArchMapDocumentV2,
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    plan: &RepairPlanDocumentV1,
    execution_plan: &LawExecutionPlanV1,
) -> SagaGroundedMeasurementV1 {
    let grounding = plan.grounding.as_ref().and_then(Value::as_object);
    let grounding_ref = grounding
        .and_then(|grounding| grounding.get("surfaceRef"))
        .and_then(Value::as_str)
        .map(str::to_string)
        .unwrap_or_else(|| format!("repair-plan:{}#grounding", plan.id));
    let criterion = execution_plan.stage3_defect_source.as_ref().map(|source| {
        format!(
            "law-surface:{}#defectSources/{}/holdsCriterion",
            execution_plan.surface_id, source.law_id
        )
    });
    let Some(source) = execution_plan.stage3_defect_source.as_ref() else {
        return grounded_not_computed(
            "grounded_surface_defect_source_missing",
            grounding_ref,
            execution_plan,
        );
    };
    let grounded_variable_aliases = execution_plan.grounded_variable_aliases.as_ref();
    let grounded_forbidden_supports = execution_plan.grounded_forbidden_supports.as_ref();
    let grounded_witness_variables = grounded_variable_aliases
        .into_iter()
        .flat_map(|aliases| aliases.values())
        .cloned()
        .collect::<BTreeSet<_>>();
    let grounding_is_aligned = grounding.is_some_and(|grounding| {
        grounding.get("kind").and_then(Value::as_str) == Some("saga-grounding")
            && grounding.get("profileRef").and_then(Value::as_str)
                == Some(profile.profile_id.as_str())
            && grounding.get("surfaceRef").and_then(Value::as_str)
                == Some(execution_plan.surface_id.as_str())
    });
    let skeleton_is_aligned = execution_plan
        .stage3_skeleton
        .as_ref()
        .is_some_and(|skeleton| {
            !skeleton.is_empty()
                && skeleton
                    .iter()
                    .map(|simplex| simplex.support_atom_ref.as_str())
                    .collect::<BTreeSet<_>>()
                    .len()
                    == skeleton.len()
                && skeleton.iter().all(|simplex| {
                    !simplex.support_atom_ref.is_empty()
                        && simplex.required_law_id == execution_plan.selected_law_id
                        && normalized
                            .atoms
                            .iter()
                            .any(|atom| atom.normalized_atom_id == simplex.support_atom_ref)
                })
        });
    let coefficient_is_f2 = profile.coefficient == "F2"
        && (plan.coefficient.is_f2_additive()
            || plan.coefficient.supplied().is_some_and(|coefficient| {
                coefficient.kind == "f2-additive"
                    && coefficient.characteristic == 2
                    && coefficient.additive
                    && coefficient.delta_one_after_delta_zero
                    && coefficient.zero_maps_to_zero
            }));
    let defect_support_size = source
        .chart_defects
        .iter()
        .flat_map(|chart| {
            normalized.atoms.iter().filter(|atom| {
                atom.axis == chart.defect_observable.axis
                    && atom.predicate == chart.defect_observable.predicate
                    && atom.context_memberships.iter().any(|context| {
                        context == &chart.chart || context == &format!("ctx:{}", chart.chart)
                    })
            })
        })
        .count();
    if !grounding_is_aligned
        || !skeleton_is_aligned
        || !coefficient_is_f2
        || plan.faithfulness.mode != "supplied"
        || plan.faithfulness.supplied.is_none()
        || plan.comparison.is_none()
        || class_supply_is_checked(archmap, plan).is_none()
        || grounded_variable_aliases.is_none()
        || grounded_forbidden_supports.is_none()
        || grounded_witness_variables.is_empty()
        || grounded_witness_variables.len() + defect_support_size
            > profile.finite_bounds.max_square_free_witness_variables
        || source.cover_ref != profile.cover_ref
        || defect_support_size > profile.finite_bounds.max_square_free_witness_variables
        || execution_plan.stage3_skeleton.is_none()
        || execution_plan.stage3_quotient_sheaf_condition.is_none()
        || execution_plan
            .stage3_quotient_sheaf_condition
            .as_ref()
            .is_some_and(|condition| condition.mode == "not-selected")
    {
        return grounded_not_computed(
            if !grounding_is_aligned {
                "grounding_reference_mismatch"
            } else if !skeleton_is_aligned {
                "grounded_skeleton_not_aligned"
            } else if !coefficient_is_f2 {
                "grounded_coefficient_not_f2_additive"
            } else if plan.faithfulness.mode != "supplied"
                || plan.faithfulness.supplied.is_none()
                || plan.comparison.is_none()
                || class_supply_is_checked(archmap, plan).is_none()
            {
                "grounded_layer_d_not_supplied"
            } else if source.cover_ref != profile.cover_ref {
                "grounded_cover_profile_mismatch"
            } else if grounded_variable_aliases.is_none()
                || grounded_forbidden_supports.is_none()
                || grounded_witness_variables.is_empty()
            {
                "grounded_equation_support_not_supplied"
            } else if grounded_witness_variables.len() + defect_support_size
                > profile.finite_bounds.max_square_free_witness_variables
            {
                "grounded_witness_variable_bound_exceeded"
            } else if defect_support_size > profile.finite_bounds.max_square_free_witness_variables
            {
                "grounded_finite_bound_exceeded"
            } else {
                "grounding_or_quotient_contract_missing"
            },
            grounding_ref,
            execution_plan,
        );
    }
    let per_chart = source
        .chart_defects
        .iter()
        .map(|chart| {
            let normalized_chart = if chart.chart.starts_with("ctx:") {
                chart.chart.clone()
            } else {
                format!("ctx:{}", chart.chart)
            };
            let atom_refs = normalized
                .atoms
                .iter()
                .filter(|atom| {
                    atom.axis == chart.defect_observable.axis
                        && atom.predicate == chart.defect_observable.predicate
                        && atom.context_memberships.contains(&normalized_chart)
                })
                .map(|atom| atom.normalized_atom_id.clone())
                .collect::<Vec<_>>();
            let support_variables = atom_refs.clone();
            let holds = match source.holds_criterion.zero_sense.as_str() {
                "empty-witness-set" => atom_refs.is_empty(),
                _ => false,
            };
            json!({
                "chart": chart.chart,
                "law": source.law_id,
                "holds": holds,
                "holdsCriterionRef": criterion,
                "defectValueRef": format!("{}#{}", normalized.source_archmap_ref, normalized_chart),
                "rawAtomRefs": atom_refs,
                "supportVariables": support_variables,
                "defectObservable": {
                    "axis": chart.defect_observable.axis,
                    "predicate": chart.defect_observable.predicate
                }
            })
        })
        .collect::<Vec<_>>();
    let laws_hold = !per_chart.is_empty()
        && per_chart
            .iter()
            .all(|chart| chart.get("holds").and_then(Value::as_bool) == Some(true));
    let quotient_basis = grounded_witness_variables
        .iter()
        .cloned()
        .chain(
            per_chart
                .iter()
                .flat_map(|chart| chart["supportVariables"].as_array().into_iter().flatten())
                .filter_map(Value::as_str)
                .map(str::to_string),
        )
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let observed_support = per_chart
        .iter()
        .flat_map(|chart| chart["supportVariables"].as_array().into_iter().flatten())
        .filter_map(Value::as_str)
        .map(str::to_string)
        .collect::<BTreeSet<_>>();
    let interpretation_zero = observed_support.is_empty();
    let obstruction_generators = grounded_forbidden_supports
        .into_iter()
        .flat_map(|supports| supports.iter().enumerate())
        .map(|(index, support)| {
            let support = support
                .iter()
                .filter_map(|variable| {
                    grounded_variable_aliases.and_then(|aliases| aliases.get(variable))
                })
                .cloned()
                .collect::<Vec<_>>();
            let support_atom_refs = support
                .iter()
                .filter(|alias| {
                    normalized
                        .atoms
                        .iter()
                        .any(|atom| atom.normalized_atom_id == **alias)
                })
                .cloned()
                .collect::<Vec<_>>();
            json!({
                "generatorId": format!("grounded-forbidden-{index}"),
                "support": support,
                "supportAtomRefs": support_atom_refs
            })
        })
        .collect::<Vec<_>>();
    let interpretation_map = quotient_basis
        .iter()
        .map(|variable| {
            json!({
                "variable": variable,
                "image": format!("[{variable}]"),
                "observed": observed_support.contains(variable)
            })
        })
        .collect::<Vec<_>>();
    let representative_support = observed_support.into_iter().collect::<Vec<_>>();
    let generated_quotient = json!({
        "coefficient": "F2",
        "construction": "finite Boolean quotient of the declared chart-defect observation space",
        "ambient": {
            "basis": quotient_basis,
            "relations": ["e_i^2=e_i", "2e_i=0"]
        },
        "obstructionIdeal": {
            "generators": obstruction_generators,
            "kind": "finite-f2-boolean-obstruction-ideal",
            "source": "law-equation-surface.forbiddenSupportGenerators"
        },
        "representative": {
            "support": representative_support,
            "normalForm": representative_support,
            "reduction": "modulo the generated finite obstruction ideal"
        },
        "interpretation": {
            "map": interpretation_map,
            "class": if interpretation_zero { "zero" } else { "nonzero" },
            "representative": representative_support
        },
        "finiteBound": profile.finite_bounds.max_square_free_witness_variables,
        "finiteBoundChecked": true
    });
    let nonzero_charts = per_chart
        .iter()
        .filter(|chart| chart.get("holds").and_then(Value::as_bool) == Some(false))
        .map(|chart| {
            json!({
                "chart": chart["chart"],
                "law": chart["law"],
                "interpretationClass": "nonzero",
                "reading": "非零 interpretation はこの chart の displayed required law の失敗を保証する(系11.5 detector soundness。前提計算は本 run の測定)"
            })
        })
        .collect::<Vec<_>>();
    let status = if laws_hold {
        "established"
    } else {
        "not_established"
    };
    let conclusion_status =
        |theorem_ref: &str| json!({"status": status, "theoremRef": theorem_ref});
    let law_dependent = json!({
        "premise": {
            "name": "displayedRequiredLawsHold",
            "status": if laws_hold { "holds" } else { "fails" },
            "checkKind": "holds-criterion-raw-value",
            "perChart": per_chart
        },
        "conclusions": {
            "generatedInterpretationZero": {
                "status": if interpretation_zero { status } else { "not_established" },
                "theoremRef": "part10/7.5.1",
                "instanceReading": {"class": if interpretation_zero { "zero" } else { "nonzero" }}
            },
            "generatedRestrictionEvaluator": conclusion_status("part3/11.4"),
            "nonzeroInterpretationDetectsDisplayedLawFailure": conclusion_status("part10/7.5.3")
        },
        "detectorFindings": nonzero_charts
    });
    let law_independent = json!({
        "note": "以下は law の充足を仮定せずに従う(定理8.2)。law 充足の証拠として読まない。",
        "conclusions": {
            "groundedGlobalGluingPackage": {"status": "established", "theoremRef": "part10/7.3"},
            "sheafConditionForSelectedCover": {"status": "established", "theoremRef": "part10/7.3"},
            "descent": {"status": "established", "theoremRef": "part10/6.6", "note": "sheaf 条件 + cover membership から導出。独立 certificate は受け取らない"},
            "uniqueGlobalSection": {"status": "established", "theoremRef": "part10/7.3"},
            "globalCoherentIffCoverRelativeH1Zero": {"status": "established", "theoremRef": "part10/8.2", "instanceReading": {"coverRelativeH1Zero": true}},
            "boundedAdditiveH1ZeroIffCoverRelativeH1Zero": {"status": "established", "theoremRef": "part10/8.2"},
            "higherObstructionsVanish": {"status": "established", "theoremRef": "part10/4.8", "note": "additive regime で自明に成立。外部仮定として供給されない(定理4.8 結論5)"}
        }
    });
    let invariant = json!({
        "invariantId": "saga-generated-end-to-end-packet",
        "kind": "saga-grounded-conclusions",
        "evaluator": "ag.saga-grounded",
        "schema": ARCHSIG_SAGA_CONCLUSIONS_V1_SCHEMA,
        "groundedSurfaceRef": grounding_ref,
        "theoremRef": "part10/7.5",
        "lawDependent": law_dependent,
        "lawIndependent": law_independent,
        "degreeZeroLawContribution": {
            "theoremRef": "part10/8.1",
            "generatedC0PointwiseZero": true,
            "reading": "law 意味論が Čech 複体に到達する地点は正確に次数0。H^1 の内容は cover の幾何から来る(意味8.3)"
        },
        "generatedQuotient": generated_quotient,
        "detectorFindings": nonzero_charts,
        "detectorCount": nonzero_charts.len()
    });
    let mut assumptions = vec![AgAssumptionLedgerEntryV1 {
        theorem_ref: "part3/11.3".to_string(),
        assumption: "displayedRequiredLawsHold is operationalized only by the declared holdsCriterion raw-value check".to_string(),
        status: "checked".to_string(),
        checked_by: Some(ARCHSIG_DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS.to_string()),
        assumed_by: None,
    }];
    if execution_plan
        .stage3_quotient_sheaf_condition
        .as_ref()
        .is_some_and(|condition| condition.mode == "assumed")
    {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part10/7.3".to_string(),
            assumption: format!(
                "selected quotient sheaf condition for {}",
                execution_plan.surface_id
            ),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("law-surface:{}", execution_plan.surface_id)),
        });
    }
    let assumption_ids = assumptions
        .iter()
        .map(assumption_id_for_schema)
        .collect::<Vec<_>>();
    let verdict = if laws_hold {
        "measured_zero"
    } else {
        "measured_nonzero"
    };
    SagaGroundedMeasurementV1 {
        structural_verdict: vec![AgStructuralVerdictV1 {
            evaluator: "ag.saga-grounded".to_string(),
            law: source.law_id.clone(),
            verdict: verdict.to_string(),
            verdict_data: AgVerdictDataV1 {
                in_scope: true,
                zero: laws_hold,
                non_zero: !laws_hold,
                method_status: if laws_hold {
                    "holds_criterion_raw_value_zero"
                } else {
                    "law_defect_detected"
                }
                .to_string(),
                cert_ref: Some("computedInvariants/saga-generated-end-to-end-packet".to_string()),
            },
            depends_on_assumptions: assumption_ids,
            reason: Some(if laws_hold {
                ARCHSIG_DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS.to_string()
            } else {
                ARCHSIG_MEASURED_LAW_DEFECT_AT_CHART.to_string()
            }),
        }],
        computed_invariants: vec![invariant],
        assumptions,
    }
}

fn grounded_not_computed(
    reason: &str,
    grounding_ref: String,
    execution_plan: &LawExecutionPlanV1,
) -> SagaGroundedMeasurementV1 {
    SagaGroundedMeasurementV1 {
        structural_verdict: vec![AgStructuralVerdictV1 {
            evaluator: "ag.saga-grounded".to_string(),
            law: execution_plan.selected_law_id.clone(),
            verdict: "not_computed".to_string(),
            verdict_data: AgVerdictDataV1 {
                in_scope: true,
                zero: false,
                non_zero: false,
                method_status: reason.to_string(),
                cert_ref: None,
            },
            depends_on_assumptions: Vec::new(),
            reason: Some(format!("ag.saga-grounded is silent by design: {reason}")),
        }],
        computed_invariants: vec![json!({
            "invariantId": "saga-generated-end-to-end-packet",
            "kind": "saga-grounded-conclusions",
            "evaluator": "ag.saga-grounded",
            "schema": ARCHSIG_SAGA_CONCLUSIONS_V1_SCHEMA,
            "groundedSurfaceRef": grounding_ref,
            "status": "not_computed",
            "methodStatus": reason
        })],
        assumptions: Vec::new(),
    }
}

pub(crate) fn evaluate_saga_descent_v1(
    archmap: &ArchMapDocumentV2,
    plan: &RepairPlanDocumentV1,
) -> SagaDescentMeasurementV1 {
    let boundary = solve_boundary_membership(plan);
    let closure = closure_diagnostics(archmap, plan);
    let enumeration_assumption = AgAssumptionLedgerEntryV1 {
        theorem_ref: "part10/3.1".to_string(),
        assumption: format!(
            "repair-plan complex enumeration completeness for {}",
            plan.id
        ),
        status: "assumed".to_string(),
        checked_by: None,
        assumed_by: Some("repair-plan author".to_string()),
    };
    let enumeration_assumption_id = assumption_id_for_schema(&enumeration_assumption);
    let comparison_target_enumeration_assumption = plan
        .comparison
        .as_ref()
        .filter(|comparison| {
            comparison
                .get("incidenceBridge")
                .and_then(|bridge| bridge.get("kind"))
                .and_then(Value::as_str)
                == Some("explicit")
        })
        .and_then(|comparison| comparison_target_complex(plan, comparison))
        .map(|_| AgAssumptionLedgerEntryV1 {
            theorem_ref: "part10/6.2".to_string(),
            assumption: format!(
                "comparison target complex enumeration completeness for {}",
                plan.id
            ),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some("comparison author".to_string()),
        });
    let sheaf_assumption =
        plan.true_sheaf_certificate
            .as_ref()
            .and_then(Value::as_object)
            .and_then(|certificate| {
                (certificate.get("globalCondition").and_then(Value::as_str) == Some("assumed"))
                    .then(|| AgAssumptionLedgerEntryV1 {
                        theorem_ref: "part10/8.1".to_string(),
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
    if let Some(assumption) = comparison_target_enumeration_assumption.as_ref() {
        evaluator_assumption_ids.push(assumption_id_for_schema(assumption));
    }
    if let Some(assumption) = faithfulness_assumption.as_ref() {
        evaluator_assumption_ids.push(assumption_id_for_schema(assumption));
    }
    let mut class_assumption_ids = evaluator_assumption_ids.clone();
    if let Some(assumption) = sheaf_assumption.as_ref() {
        class_assumption_ids.push(assumption_id_for_schema(assumption));
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
    if let Some(class_certificate) = class_supply_is_checked(archmap, plan) {
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
            depends_on_assumptions: class_assumption_ids.clone(),
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
                "component": {
                    "chartRefs": &class_certificate.cocycle.component.chart_refs,
                    "overlapRefs": &class_certificate.cocycle.component.overlap_refs
                },
                "cocycle": {
                    "checked": true,
                    "deltaOne": "zero",
                    "certificateKind": class_certificate.cocycle.certificate_kind,
                    "tripleOverlapRefs": class_certificate.cocycle.triple_overlap_refs_json()
                },
                "suppliedData": {
                    "trueSheafCertificate": {
                        "coverRef": &class_certificate.true_sheaf_cover_ref,
                        "memberChartRefs": &class_certificate.true_sheaf_member_chart_refs,
                        "globalCondition": &class_certificate.true_sheaf_global_condition
                    },
                    "gluingData": {
                        "overlapRefs": class_certificate.gluing_overlap_refs(),
                        "sectionRefs": class_certificate.gluing_section_refs_json()
                    }
                }
            },
            "suppliedSlots": [
                "complex.charts",
                "complex.overlaps",
                "coefficient",
                "trueSheafCertificate",
                "gluingData"
            ]
        }));
    }
    computed_invariants.push(evaluate_saga_comparison_v1(plan, &structural_verdict));
    let mut assumptions = vec![enumeration_assumption];
    if let Some(comparison_target_enumeration_assumption) = comparison_target_enumeration_assumption
    {
        assumptions.push(comparison_target_enumeration_assumption);
    }
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
            "reason": "comparison_data_not_supplied",
            "whatNext": "supply a validated incidence bridge and H1 comparison contract before evaluating transfer",
            "contract": {
                "incidenceBridgeKind": "not_supplied",
                "h1ComparisonDataKind": "not_supplied",
                "normalizedComplexFingerprint": comparison_complex_fingerprint(plan),
                "classPrerequisite": false,
                "targetClassComputed": false,
                "contractChecked": false
            }
        });
    };
    let measured_class_available = structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.saga-descent"
            && verdict.law == "saga.residual-class"
            && matches!(
                verdict.verdict.as_str(),
                "measured_zero" | "measured_nonzero"
            )
    });
    let measured_class_nonzero = structural_verdict.iter().any(|verdict| {
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
    let explicit_checks = if h1_kind == "explicit" {
        comparison_target_complex(plan, comparison).and_then(|target_complex| {
            comparison
                .get("h1ComparisonData")
                .and_then(Value::as_object)
                .map(|h1| explicit_h1_comparison_checks(plan, &target_complex, h1))
        })
    } else {
        None
    };
    let presentation_checks = if h1_kind == "presentation-generated" {
        comparison_target_complex(plan, comparison).and_then(|target_complex| {
            comparison
                .get("h1ComparisonData")
                .and_then(Value::as_object)
                .map(|h1| presentation_generated_h1_checks(plan, &target_complex, h1))
        })
    } else {
        None
    };
    let contract_checked = if h1_kind == "explicit" {
        explicit_checks.is_some_and(|checks| checks.all_pass())
    } else if h1_kind == "presentation-generated" {
        presentation_checks
            .as_ref()
            .is_some_and(|checks| checks.all_pass())
    } else {
        true
    };
    let (class_available, class_nonzero, source_invariant) = if h1_kind == "presentation-generated"
    {
        presentation_checks
            .as_ref()
            .and_then(|checks| checks.source_class_nonzero)
            .map(|source_class_nonzero| {
                (
                    true,
                    source_class_nonzero,
                    "presentation-generated:semantic-h1-class",
                )
            })
            .unwrap_or((false, false, "presentation-generated:semantic-h1-class"))
    } else {
        (
            measured_class_available,
            measured_class_nonzero,
            "saga-descent:residual-class",
        )
    };
    let target_class_nonzero = if h1_kind == "presentation-generated" {
        presentation_checks
            .as_ref()
            .and_then(|checks| checks.target_class_nonzero)
    } else {
        comparison_target_class_nonzero(plan, comparison)
    };
    let preserves_zero_predicate =
        target_class_nonzero.is_some_and(|target| target == class_nonzero);
    let comparison_contract_violation = class_available
        && target_class_nonzero.is_some()
        && (!contract_checked || !preserves_zero_predicate);
    if !class_available {
        let (reason, what_next, non_conclusions) = if h1_kind == "presentation-generated" {
            (
                "presentation_source_class_prerequisite_not_computed",
                "supply a valid semantic presentation, restriction maps, and equation lift atlas so the source presentation H1 class can be computed before evaluating transfer",
                [
                    "The comparison contract is not a replacement for the computed source presentation H1 class.",
                    "No comparison failure code is emitted until the source presentation H1 class is computed.",
                ],
            )
        } else {
            (
                "residual_class_prerequisite_not_measured",
                "supply an F2 coefficient, a valid cocycle certificate for the residual component, and trueSheafCertificate plus gluingData that each match that component exactly so the source residual class can be measured before evaluating H1 comparison transfer",
                [
                    "The comparison contract is not a replacement for the measured source residual class.",
                    "No comparison failure code is emitted until the residual-class prerequisite is measured.",
                ],
            )
        };
        return json!({
            "invariantId": "saga-comparison:h1-transfer",
            "evaluator": "ag.saga-comparison",
            "kind": "h1-comparison-transfer",
            "status": "silence_by_design",
            "reason": reason,
            "whatNext": what_next,
            "contract": {
                "incidenceBridgeKind": bridge_kind,
                "h1ComparisonDataKind": h1_kind,
                "normalizedComplexFingerprint": comparison_complex_fingerprint(plan),
                "classPrerequisite": false,
                "targetClassComputed": target_class_nonzero.is_some(),
                "contractChecked": contract_checked
            },
            "nonConclusions": non_conclusions
        });
    }
    let established = contract_checked && class_available && preserves_zero_predicate;
    let conclusion_code = if established {
        if h1_kind == "presentation-generated" {
            Some(ARCHSIG_SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS)
        } else {
            Some(ARCHSIG_SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA)
        }
    } else {
        None
    };
    let presentation_generated = if h1_kind == "presentation-generated" {
        comparison_target_complex(plan, comparison)
            .zip(
                comparison
                    .get("h1ComparisonData")
                    .and_then(Value::as_object),
            )
            .zip(presentation_checks.as_ref())
            .map(|((target_complex, h1), checks)| {
                presentation_generated_h1_output(plan, &target_complex, h1, checks)
            })
            .unwrap_or(Value::Null)
    } else {
        Value::Null
    };
    json!({
        "invariantId": "saga-comparison:h1-transfer",
        "evaluator": "ag.saga-comparison",
        "kind": "h1-comparison-transfer",
        "status": if established { "established" } else { "not_computed" },
        "conclusionCode": conclusion_code,
        "contract": {
            "incidenceBridgeKind": bridge_kind,
            "h1ComparisonDataKind": h1_kind,
            "normalizedComplexFingerprint": comparison_complex_fingerprint(plan),
            "classPrerequisite": class_available,
            "targetClassComputed": target_class_nonzero.is_some(),
            "contractChecked": contract_checked
        },
        "suppliedCochainMap": {
            "level": "cochain",
            "kind": h1_kind,
            "contractChecked": (h1_kind == "explicit").then_some(contract_checked),
            "checkedProperties": explicit_checks.map(|checks| json!({
                "degreeOneLeftInverse": checks.degree_one_left_inverse,
                "degreeOneRightInverse": checks.degree_one_right_inverse,
                "differencePreserving": checks.difference_preserving,
                "degreeTwoZeroPreserving": checks.degree_two_zero_preserving,
                "differentialCommutative": checks.differential_commutative
            })),
            "targetSupportComputed": target_class_nonzero.is_some()
        },
        "presentationGenerated": presentation_generated,
        "generatedQuotientTransfer": if established {
            json!({
                "level": "quotient",
                "kind": if h1_kind == "presentation-generated" {
                    "presentation-derived-Z1/B1-class-transfer"
                } else {
                    "Z1/B1-class-transfer"
                },
                "preservesZeroPredicate": preserves_zero_predicate,
                "sourceClassNonZero": class_nonzero,
                "targetClassNonZero": target_class_nonzero,
                "sourceInvariant": source_invariant,
                "targetInvariant": "saga-comparison:h1-transfer"
            })
        } else {
            Value::Null
        },
        "failureCode": if comparison_contract_violation {
            json!(ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION)
        } else {
            Value::Null
        },
        "nonConclusions": [
            "Supplied cochain data and generated quotient-level transfer are separate structures.",
            "The transfer reading is relative to the supplied finite comparison contract."
        ]
    })
}

fn comparison_target_class_nonzero(
    plan: &RepairPlanDocumentV1,
    comparison: &Value,
) -> Option<bool> {
    let target_complex = comparison_target_complex(plan, comparison)?;
    let h1 = comparison.get("h1ComparisonData")?.as_object()?;
    let items = h1.get("targetCochainSupport")?.as_array()?;
    let mut support_by_overlap = BTreeMap::<&str, BTreeSet<&str>>::new();
    for item in items {
        let object = item.as_object()?;
        let overlap_ref = object.get("overlapRef")?.as_str()?;
        let support = object.get("support")?.as_array()?;
        let variables = support
            .iter()
            .map(Value::as_str)
            .collect::<Option<Vec<_>>>()?;
        let variable_set = variables.iter().copied().collect::<BTreeSet<_>>();
        if variables.len() != variable_set.len()
            || support_by_overlap
                .insert(overlap_ref, variable_set)
                .is_some()
        {
            return None;
        }
    }
    if support_by_overlap.len() != target_complex.overlaps.len()
        || target_complex
            .overlaps
            .iter()
            .any(|overlap| !support_by_overlap.contains_key(overlap.id.as_str()))
    {
        return None;
    }
    let mut target_plan = plan.clone();
    target_plan.complex = target_complex;
    for primitive in &mut target_plan.primitives {
        primitive.support.variables = support_by_overlap
            .get(primitive.overlap_ref.as_str())?
            .iter()
            .map(|variable| (*variable).to_string())
            .collect();
    }
    Some(!solve_boundary_membership(&target_plan).in_b1)
}

#[derive(Debug, Clone)]
struct RepairComplexComponent {
    chart_refs: Vec<String>,
    overlap_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct SagaComponentCocycleCertificate {
    component: RepairComplexComponent,
    certificate_kind: &'static str,
    triple_overlaps: Vec<(String, Vec<String>)>,
}

impl SagaComponentCocycleCertificate {
    fn triple_overlap_refs_json(&self) -> Vec<Value> {
        self.triple_overlaps
            .iter()
            .map(|(triple_ref, overlap_refs)| {
                json!({
                    "tripleRef": triple_ref,
                    "overlapRefs": overlap_refs
                })
            })
            .collect()
    }
}

#[derive(Debug, Clone)]
struct SagaClassSupplyCertificate {
    cocycle: SagaComponentCocycleCertificate,
    true_sheaf_cover_ref: String,
    true_sheaf_member_chart_refs: Vec<String>,
    true_sheaf_global_condition: String,
    gluing_section_refs: Vec<(String, String)>,
}

impl SagaClassSupplyCertificate {
    fn gluing_overlap_refs(&self) -> Vec<&str> {
        self.gluing_section_refs
            .iter()
            .map(|(overlap_ref, _)| overlap_ref.as_str())
            .collect()
    }

    fn gluing_section_refs_json(&self) -> Vec<Value> {
        self.gluing_section_refs
            .iter()
            .map(|(overlap_ref, section_ref)| {
                json!({
                    "overlapRef": overlap_ref,
                    "sectionRef": section_ref
                })
            })
            .collect()
    }
}

fn class_supply_is_checked(
    archmap: &ArchMapDocumentV2,
    plan: &RepairPlanDocumentV1,
) -> Option<SagaClassSupplyCertificate> {
    let cocycle = component_cocycle_certificate(plan)?;
    let coefficient_ok = coefficient_is_f2_additive(plan);
    let (true_sheaf_cover_ref, true_sheaf_member_chart_refs, true_sheaf_global_condition) =
        component_true_sheaf_certificate(archmap, plan, &cocycle.component)?;
    let gluing_section_refs = component_gluing_data(plan, &cocycle.component)?;
    coefficient_ok.then_some(SagaClassSupplyCertificate {
        cocycle,
        true_sheaf_cover_ref,
        true_sheaf_member_chart_refs,
        true_sheaf_global_condition,
        gluing_section_refs,
    })
}

fn component_true_sheaf_certificate(
    archmap: &ArchMapDocumentV2,
    plan: &RepairPlanDocumentV1,
    component: &RepairComplexComponent,
) -> Option<(String, Vec<String>, String)> {
    let certificate = plan.true_sheaf_certificate.as_ref()?.as_object()?;
    let global_condition = certificate.get("globalCondition").and_then(Value::as_str)?;
    if certificate.get("kind").and_then(Value::as_str) != Some("true-sheaf-certificate")
        || global_condition != "assumed"
    {
        return None;
    }
    let cover_ref = certificate.get("coverRef")?.as_str()?;
    let cover = archmap.covers.iter().find(|cover| cover.id == cover_ref)?;
    let component_chart_refs = component
        .chart_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let member_charts = certificate
        .get("memberCharts")?
        .as_array()?
        .iter()
        .map(Value::as_str)
        .collect::<Option<Vec<_>>>()?;
    let cover_charts = cover
        .contexts
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>();
    let has_exact_component_charts = |charts: &[&str]| {
        charts.len() == component_chart_refs.len()
            && charts.iter().copied().collect::<BTreeSet<_>>() == component_chart_refs
    };
    (has_exact_component_charts(&member_charts) && has_exact_component_charts(&cover_charts))
        .then_some((
            cover_ref.to_string(),
            component.chart_refs.clone(),
            global_condition.to_string(),
        ))
}

fn component_gluing_data(
    plan: &RepairPlanDocumentV1,
    component: &RepairComplexComponent,
) -> Option<Vec<(String, String)>> {
    let gluing = plan.gluing_data.as_ref()?.as_object()?;
    if gluing.get("kind").and_then(Value::as_str) != Some("gluing-data") {
        return None;
    }
    let component_overlap_refs = component
        .overlap_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let overlap_refs = gluing
        .get("overlapRefs")?
        .as_array()?
        .iter()
        .map(Value::as_str)
        .collect::<Option<Vec<_>>>()?;
    if overlap_refs.len() != component_overlap_refs.len()
        || overlap_refs.iter().copied().collect::<BTreeSet<_>>() != component_overlap_refs
    {
        return None;
    }
    let section_refs = gluing
        .get("sectionRefs")?
        .as_array()?
        .iter()
        .map(|item| {
            let item = item.as_object()?;
            let overlap_ref = item.get("overlapRef")?.as_str()?;
            let section_ref = item.get("sectionRef")?.as_str()?;
            (canonical_section_ref(overlap_ref).as_deref() == Some(section_ref))
                .then_some((overlap_ref, section_ref))
        })
        .collect::<Option<Vec<_>>>()?;
    let supplied_overlaps = section_refs
        .iter()
        .map(|(overlap_ref, _)| *overlap_ref)
        .collect::<BTreeSet<_>>();
    let supplied_sections = section_refs
        .iter()
        .map(|(_, section_ref)| *section_ref)
        .collect::<BTreeSet<_>>();
    if section_refs.len() != component_overlap_refs.len()
        || supplied_overlaps != component_overlap_refs
        || supplied_sections.len() != component_overlap_refs.len()
    {
        return None;
    }
    let mut section_refs = section_refs
        .into_iter()
        .map(|(overlap_ref, section_ref)| (overlap_ref.to_string(), section_ref.to_string()))
        .collect::<Vec<_>>();
    section_refs.sort_by(|left, right| left.0.cmp(&right.0));
    Some(section_refs)
}

fn canonical_section_ref(overlap_ref: &str) -> Option<String> {
    overlap_ref
        .strip_prefix("overlap:")
        .filter(|suffix| !suffix.is_empty())
        .map(|suffix| format!("section:{suffix}"))
}

fn coefficient_is_f2_additive(plan: &RepairPlanDocumentV1) -> bool {
    plan.coefficient.is_f2_additive()
        || plan.coefficient.supplied().is_some_and(|coefficient| {
            coefficient.kind == "f2-additive"
                && coefficient.characteristic == 2
                && coefficient.additive
                && coefficient.delta_one_after_delta_zero
                && coefficient.zero_maps_to_zero
        })
}

fn component_cocycle_certificate(
    plan: &RepairPlanDocumentV1,
) -> Option<SagaComponentCocycleCertificate> {
    if !plan.complex.enumeration_complete {
        return None;
    }
    let component = residual_support_component(plan)?;
    let component_overlap_refs = component
        .overlap_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let component_triples = plan
        .complex
        .triple_overlaps
        .iter()
        .filter(|triple| {
            triple
            .overlap_refs
            .iter()
            .any(|overlap_ref| component_overlap_refs.contains(overlap_ref.as_str()))
        })
        .cloned()
        .collect::<Vec<_>>();
    let component_complex = RepairPlanComplexV1 {
        charts: component.chart_refs.clone(),
        overlaps: plan
            .complex
            .overlaps
            .iter()
            .filter(|overlap| component_overlap_refs.contains(overlap.id.as_str()))
            .cloned()
            .collect(),
        triple_overlaps: component_triples.clone(),
        archmap_cover_ref: plan.complex.archmap_cover_ref.clone(),
        enumeration_complete: true,
    };
    if !complex_has_valid_finite_incidence(&component_complex) {
        return None;
    }
    let mut triple_overlaps = Vec::new();
    for triple in &component_triples {
        let refs = triple
            .overlap_refs
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        if triple.overlap_refs.len() != 3
            || refs.len() != 3
            || !refs.is_subset(&component_overlap_refs)
            || !triple_cocycle_is_zero(plan, &triple.overlap_refs)
        {
            return None;
        }
        triple_overlaps.push((triple.id.clone(), triple.overlap_refs.clone()));
    }
    triple_overlaps.sort_by(|left, right| left.0.cmp(&right.0));
    let certificate_kind = if triple_overlaps.is_empty() {
        "automatic-c2-zero"
    } else {
        "checked-triple-cocycle-zero"
    };
    Some(SagaComponentCocycleCertificate {
        component,
        certificate_kind,
        triple_overlaps,
    })
}

fn residual_support_component(plan: &RepairPlanDocumentV1) -> Option<RepairComplexComponent> {
    let components = repair_complex_components(plan)?;
    let mut component_by_overlap = BTreeMap::new();
    for (component_index, component) in components.iter().enumerate() {
        for overlap_ref in &component.overlap_refs {
            component_by_overlap.insert(overlap_ref.as_str(), component_index);
        }
    }
    let mut residual_overlap_refs = plan
        .primitives
        .iter()
        .filter(|primitive| !primitive.support.variables.is_empty())
        .map(|primitive| primitive.overlap_ref.as_str())
        .collect::<BTreeSet<_>>();
    if residual_overlap_refs.is_empty() {
        let zero_primitive_ref = plan.faithfulness.supplied.as_ref()?.zero_primitive_ref.as_str();
        let zero_primitive = plan
            .primitives
            .iter()
            .find(|primitive| primitive.id == zero_primitive_ref)?;
        if !zero_primitive.support.variables.is_empty() {
            return None;
        }
        residual_overlap_refs.insert(zero_primitive.overlap_ref.as_str());
    }
    let mut selected_component = None;
    for overlap_ref in residual_overlap_refs {
        let component_index = *component_by_overlap.get(overlap_ref)?;
        if selected_component.replace(component_index).is_some_and(|previous| previous != component_index)
        {
            return None;
        }
    }
    selected_component.and_then(|index| components.get(index).cloned())
}

fn repair_complex_components(plan: &RepairPlanDocumentV1) -> Option<Vec<RepairComplexComponent>> {
    let chart_refs = plan
        .complex
        .charts
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    if chart_refs.len() != plan.complex.charts.len() {
        return None;
    }
    let mut neighbors = chart_refs
        .iter()
        .cloned()
        .map(|chart_ref| (chart_ref, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    let mut overlap_ids = BTreeSet::new();
    for overlap in &plan.complex.overlaps {
        if !overlap_ids.insert(overlap.id.as_str())
            || !chart_refs.contains(&overlap.left)
            || !chart_refs.contains(&overlap.right)
        {
            return None;
        }
        neighbors
            .get_mut(&overlap.left)?
            .insert(overlap.right.clone());
        neighbors
            .get_mut(&overlap.right)?
            .insert(overlap.left.clone());
    }
    let mut unvisited = chart_refs;
    let mut components = Vec::new();
    while let Some(start) = unvisited.iter().next().cloned() {
        let mut component_charts = BTreeSet::new();
        let mut pending = vec![start];
        while let Some(chart_ref) = pending.pop() {
            if !unvisited.remove(&chart_ref) {
                continue;
            }
            component_charts.insert(chart_ref.clone());
            pending.extend(
                neighbors
                    .get(&chart_ref)?
                    .iter()
                    .filter(|neighbor| unvisited.contains(*neighbor))
                    .cloned(),
            );
        }
        let overlap_refs = plan
            .complex
            .overlaps
            .iter()
            .filter(|overlap| {
                component_charts.contains(&overlap.left)
                    && component_charts.contains(&overlap.right)
            })
            .map(|overlap| overlap.id.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        components.push(RepairComplexComponent {
            chart_refs: component_charts.into_iter().collect(),
            overlap_refs,
        });
    }
    Some(components)
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

#[cfg(test)]
mod tests {
    use super::*;

    fn comparison_fixture() -> RepairPlanDocumentV1 {
        serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/repair_plan_comparison.json"
        ))
        .expect("comparison fixture parses as RepairPlanDocumentV1")
    }

    fn component_aware_one_cent_fixture() -> Value {
        serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/repair_plan_component_aware_one_cent.json"
        ))
        .expect("component-aware fixture parses as JSON")
    }

    #[test]
    fn component_cocycle_certificate_requires_unique_actual_triangles() {
        let local_triple = serde_json::json!({
            "id": "triple:diagnostic",
            "overlapRefs": [
                "overlap:cancel-inside-payment",
                "overlap:inside-payment-order",
                "overlap:cancel-order"
            ]
        });

        let mut nontriangular = component_aware_one_cent_fixture();
        nontriangular["primitives"][1]["resL"] = serde_json::json!(["drift:one-cent"]);
        nontriangular["primitives"][1]["support"]["variables"] =
            serde_json::json!(["drift:one-cent"]);
        nontriangular["complex"]["overlaps"][2]["right"] =
            serde_json::json!("ctx:inside-payment");
        nontriangular["complex"]["tripleOverlaps"]
            .as_array_mut()
            .expect("triple overlaps are an array")
            .push(local_triple.clone());
        let nontriangular: RepairPlanDocumentV1 =
            serde_json::from_value(nontriangular).expect("nontriangular fixture still parses");
        assert!(
            component_cocycle_certificate(&nontriangular).is_none(),
            "a three-edge list that is not a three-chart triangle must not certify C2"
        );

        let mut duplicate_id = component_aware_one_cent_fixture();
        duplicate_id["primitives"][1]["resL"] = serde_json::json!(["drift:one-cent"]);
        duplicate_id["primitives"][1]["support"]["variables"] =
            serde_json::json!(["drift:one-cent"]);
        let triples = duplicate_id["complex"]["tripleOverlaps"]
            .as_array_mut()
            .expect("triple overlaps are an array");
        triples.push(local_triple.clone());
        triples.push(local_triple);
        let duplicate_id: RepairPlanDocumentV1 =
            serde_json::from_value(duplicate_id).expect("duplicate-ID fixture still parses");
        assert!(
            component_cocycle_certificate(&duplicate_id).is_none(),
            "duplicate selected triple IDs must not certify C2"
        );
    }

    fn measured_class_verdict() -> AgStructuralVerdictV1 {
        AgStructuralVerdictV1 {
            evaluator: "ag.saga-descent".to_string(),
            law: "saga.residual-class".to_string(),
            verdict: "measured_nonzero".to_string(),
            verdict_data: AgVerdictDataV1 {
                in_scope: true,
                zero: false,
                non_zero: true,
                method_status: "nonzero_class_representative".to_string(),
                cert_ref: Some("computedInvariants/saga-descent:residual-class".to_string()),
            },
            depends_on_assumptions: Vec::new(),
            reason: None,
        }
    }

    #[test]
    fn comparison_silence_precedes_contract_failure_when_class_is_missing() {
        let plan = comparison_fixture();
        let result = evaluate_saga_comparison_v1(&plan, &[]);
        assert_eq!(result["status"], "silence_by_design");
        assert_eq!(result["reason"], "residual_class_prerequisite_not_measured");
        assert!(result.get("failureCode").is_none());
    }

    #[test]
    fn presentation_generated_silence_names_its_computed_source_class_prerequisite() {
        let mut plan: RepairPlanDocumentV1 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/repair_plan_presentation_generated_circle.json"
        ))
        .expect("presentation-generated fixture parses");
        plan.comparison.as_mut().expect("comparison exists")["h1ComparisonData"]["presentation"] =
            serde_json::json!({});

        let result = evaluate_saga_comparison_v1(&plan, &[]);
        assert_eq!(result["status"], "silence_by_design");
        assert_eq!(
            result["reason"],
            "presentation_source_class_prerequisite_not_computed"
        );
        assert!(result["whatNext"]
            .as_str()
            .is_some_and(|text| text.contains("semantic presentation")));
        assert!(result["nonConclusions"]
            .as_array()
            .is_some_and(|entries| entries.iter().all(|entry| {
                entry
                    .as_str()
                    .is_some_and(|text| text.contains("source presentation H1 class"))
            })));
        assert!(result.get("failureCode").is_none());
    }

    #[test]
    fn comparison_class_predicate_mismatch_emits_contract_failure() {
        let plan = comparison_fixture();
        let result = evaluate_saga_comparison_v1(&plan, &[measured_class_verdict()]);
        assert_eq!(result["status"], "not_computed");
        assert_eq!(
            result["failureCode"],
            ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION
        );
        assert_eq!(result["contract"]["classPrerequisite"], true);
        assert_eq!(result["contract"]["targetClassComputed"], true);
    }
}
