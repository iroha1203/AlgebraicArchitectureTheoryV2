use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};

use crate::ag_measurement::observe_cech_edge;
use crate::law_execution::LawExecutionPlanV1;
use crate::saga_complex::saga_complex_has_valid_finite_incidence;
use crate::{
    ARCHSIG_DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS, ARCHSIG_MEASURED_LAW_DEFECT_AT_CHART,
    ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS, AgAssumptionLedgerEntryV1, AgStructuralVerdictV1,
    AgVerdictDataV1, DerivedSagaComplexDataV1, DerivedSagaComplexV1, LawEquationSurfaceV1,
    MeasurementProfileV1, NormalizedArchMapV2, assumption_id_for_schema,
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

/// 観測(選択 cover の cech sectionValue)と法曲面(cech witness vocabulary)から
/// 導出した residual。overlap ごとの support は、その edge の観測 mismatch が非零のとき
/// 共有導出変数の単元集合、零のとき空集合になる。
pub(crate) const DERIVED_RESIDUAL_VARIABLE: &str = "cech:section-mismatch";

#[derive(Debug, Clone)]
pub(crate) struct DerivedResidualV1 {
    pub supports: BTreeMap<String, Vec<String>>,
    pub edges: Vec<Value>,
    pub law_surface_ref: String,
    pub cover_ref: String,
}

fn selected_cover_context_ids(
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

/// 法曲面の全 law を走査し、cech witness vocabularyを集める。context pairは
/// ArchMapのselected cover/restrictionから導出し、法曲面はinstance-specificなedgeを持たない。
fn cech_witness_variables(law_surface: &LawEquationSurfaceV1) -> BTreeSet<String> {
    law_surface
        .laws
        .iter()
        .flat_map(|law| law.witness_variables.iter())
        .filter(|witness| {
            witness.binding.axis.as_deref() == Some("cech")
                && witness.binding.predicate.as_deref() == Some("sectionValue")
        })
        .map(|witness| witness.variable.clone())
        .collect()
}

pub(crate) fn derive_residual(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    plan: &DerivedSagaComplexV1,
    law_surface: &LawEquationSurfaceV1,
) -> Result<DerivedResidualV1, String> {
    if profile.coefficient != "F2" {
        return Err(format!(
            "selected profile coefficient {} is outside the F2 saga-descent vocabulary",
            profile.coefficient
        ));
    }
    let selected = selected_cover_context_ids(normalized, profile);
    if selected.is_empty() {
        return Err(format!(
            "selected cover {} does not resolve to a normalized cover",
            profile.cover_ref
        ));
    }
    let selected_set = selected.iter().map(String::as_str).collect::<BTreeSet<_>>();
    for chart in &plan.complex.charts {
        if !selected_set.contains(chart.as_str()) {
            return Err(format!(
                "derived SAGA complex chart {chart} is outside the selected cover {}",
                profile.cover_ref
            ));
        }
    }
    let chart_set = plan
        .complex
        .charts
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let mut seen_overlap_ids = BTreeSet::new();
    let mut seen_overlap_pairs = BTreeSet::new();
    for overlap in &plan.complex.overlaps {
        if !seen_overlap_ids.insert(overlap.id.as_str()) {
            return Err(format!(
                "duplicate overlap id {} in the derived SAGA complex would overwrite a derived residual edge",
                overlap.id
            ));
        }
        let mut pair = [overlap.left.as_str(), overlap.right.as_str()];
        pair.sort_unstable();
        if !seen_overlap_pairs.insert((pair[0].to_string(), pair[1].to_string())) {
            return Err(format!(
                "unordered chart pair {} / {} appears more than once in the derived SAGA complex",
                pair[0], pair[1]
            ));
        }
    }
    let witness_variables = cech_witness_variables(law_surface);
    let mut supports = BTreeMap::new();
    let mut edges = Vec::new();
    for overlap in &plan.complex.overlaps {
        if !chart_set.contains(overlap.left.as_str()) || !chart_set.contains(overlap.right.as_str())
        {
            return Err(format!(
                "overlap {} endpoints {} / {} must be declared in complex.charts",
                overlap.id, overlap.left, overlap.right
            ));
        }
        let restriction_observed = normalized.contexts.iter().any(|context| {
            (context.normalized_context_id == overlap.left
                && context.restricts_to.contains(&overlap.right))
                || (context.normalized_context_id == overlap.right
                    && context.restricts_to.contains(&overlap.left))
        });
        if !restriction_observed {
            return Err(format!(
                "overlap {} has no observed restriction between {} and {}",
                overlap.id, overlap.left, overlap.right
            ));
        }
        let observation = observe_cech_edge(normalized, &overlap.left, &overlap.right);
        if !observation.observed {
            return Err(format!(
                "overlap {} has an unobserved cech section on {} or {}",
                overlap.id, overlap.left, overlap.right
            ));
        }
        let value = observation.value;
        let witness = if value == 1 {
            witness_variables.iter().cloned().collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        if value == 1 && witness_variables.is_empty() {
            return Err(format!(
                "measured section mismatch on overlap {} has no cech witness vocabulary in the law surface",
                overlap.id
            ));
        }
        // Čech の係数はスカラーであり、mismatch した全 edge は同じ selected section family の
        // 1-cochain を成す。共有変数がその結合を表し、edge ごとの witness variable は
        // provenance として derivation record に残る。
        let support = if value == 1 {
            vec![DERIVED_RESIDUAL_VARIABLE.to_string()]
        } else {
            Vec::new()
        };
        edges.push(json!({
            "overlapRef": overlap.id,
            "leftContextRef": overlap.left,
            "rightContextRef": overlap.right,
            "value": value,
            "witnessVariables": witness,
            "supportAtomRefs": observation.support_atom_refs
        }));
        supports.insert(overlap.id.clone(), support);
    }
    Ok(DerivedResidualV1 {
        supports,
        edges,
        law_surface_ref: law_surface.id.clone(),
        cover_ref: profile.cover_ref.clone(),
    })
}

pub(crate) fn evaluate_saga_grounded_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    plan: &DerivedSagaComplexV1,
    law_surface: &LawEquationSurfaceV1,
    execution_plan: &LawExecutionPlanV1,
) -> SagaGroundedMeasurementV1 {
    let grounding_ref = format!("law-surface:{}", execution_plan.surface_id);
    let criterion = execution_plan
        .grounded_defect_source
        .as_ref()
        .map(|source| {
            format!(
                "derived:archsig-grounding:{}#defectSource/{}/holdsCriterion",
                profile.profile_id, source.law_id
            )
        });
    let Some(source) = execution_plan.grounded_defect_source.as_ref() else {
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
    let skeleton_is_aligned = execution_plan
        .grounded_skeleton
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
    let coefficient_is_f2 = profile.coefficient == "F2";
    let residual_derivation_fault =
        derive_residual(normalized, profile, plan, law_surface).is_err();
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
    if !skeleton_is_aligned
        || !coefficient_is_f2
        || residual_derivation_fault
        || grounded_variable_aliases.is_none()
        || grounded_forbidden_supports.is_none()
        || grounded_witness_variables.is_empty()
        || grounded_witness_variables.len() + defect_support_size
            > profile.finite_bounds.max_square_free_witness_variables
        || source.cover_ref != profile.cover_ref
        || defect_support_size > profile.finite_bounds.max_square_free_witness_variables
        || execution_plan.grounded_skeleton.is_none()
        || execution_plan.stage3_quotient_sheaf_condition.is_none()
        || execution_plan
            .stage3_quotient_sheaf_condition
            .as_ref()
            .is_some_and(|condition| condition.mode == "not-selected")
    {
        return grounded_not_computed(
            if !skeleton_is_aligned {
                "grounded_skeleton_not_aligned"
            } else if !coefficient_is_f2 {
                "grounded_coefficient_not_f2_additive"
            } else if residual_derivation_fault {
                "grounded_residual_derivation_fault"
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
    let invariant = json!({
        "invariantId": "saga-grounded:defect-quotient",
        "kind": "saga-grounded-defect-quotient",
        "evaluator": "ag.saga-grounded",
        "groundedSurfaceRef": grounding_ref,
        "displayedRequiredLawsHold": {
            "status": if laws_hold { "holds" } else { "fails" },
            "checkKind": "holds-criterion-raw-value",
            "perChart": per_chart
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
            theorem_ref: "part10/8.3".to_string(),
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
                cert_ref: Some("computedInvariants/saga-grounded:defect-quotient".to_string()),
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
            "invariantId": "saga-grounded:defect-quotient",
            "kind": "saga-grounded-defect-quotient",
            "evaluator": "ag.saga-grounded",
            "groundedSurfaceRef": grounding_ref,
            "status": "not_computed",
            "methodStatus": reason
        })],
        assumptions: Vec::new(),
    }
}

fn descent_not_computed(plan: &DerivedSagaComplexV1, fault: String) -> SagaDescentMeasurementV1 {
    let verdict_row = |law: &str| AgStructuralVerdictV1 {
        evaluator: "ag.saga-descent".to_string(),
        law: law.to_string(),
        verdict: "not_computed".to_string(),
        verdict_data: AgVerdictDataV1 {
            in_scope: true,
            zero: false,
            non_zero: false,
            method_status: "residual_derivation_fault".to_string(),
            cert_ref: Some("computedInvariants/saga-descent:residual-derivation".to_string()),
        },
        depends_on_assumptions: Vec::new(),
        reason: Some(fault.clone()),
    };
    SagaDescentMeasurementV1 {
        structural_verdict: vec![verdict_row("saga.residual-boundary-membership")],
        computed_invariants: vec![json!({
            "invariantId": "saga-descent:residual-derivation",
            "evaluator": "ag.saga-descent",
            "representation": {
                "invariantId": "saga-descent:residual-derivation",
                "evaluator": "ag.saga-descent"
            },
            "residualDerivation": {
                "derived": false,
                "fault": fault,
                "edges": [],
                "derivedComplexRef": plan.id,
                "derivedFrom": ["ArchMap.cover", "ArchMap.contexts.restrictsTo"]
            }
        })],
        assumptions: Vec::new(),
    }
}

pub(crate) fn evaluate_saga_descent_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    plan: &DerivedSagaComplexV1,
    law_surface: Option<&LawEquationSurfaceV1>,
) -> SagaDescentMeasurementV1 {
    let derived = match law_surface {
        None => {
            Err("saga-descent requires a supplied law surface for residual derivation".to_string())
        }
        Some(surface) => derive_residual(normalized, profile, plan, surface),
    };
    let derived = match derived {
        Err(fault) => return descent_not_computed(plan, fault),
        Ok(derived) => derived,
    };
    let boundary = solve_boundary_membership(plan, &derived.supports);
    let enumeration_assumption = AgAssumptionLedgerEntryV1 {
        theorem_ref: "part10/3.1".to_string(),
        assumption: format!("ArchSig-derived finite complex enumeration for {}", plan.id),
        status: "assumed".to_string(),
        checked_by: None,
        assumed_by: Some("ArchSig finite-complex derivation".to_string()),
    };
    let enumeration_assumption_id = assumption_id_for_schema(&enumeration_assumption);
    let evaluator_assumption_ids = vec![enumeration_assumption_id.clone()];
    let class_assumption_ids = evaluator_assumption_ids.clone();
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
            "derived residual lies in B1 for the finite complex derived from the selected ArchMap cover".to_string()
        } else {
            "derived residual is not in B1 for the finite complex derived from the selected ArchMap cover".to_string()
        }),
    });

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
            "invariantId": "saga-descent:residual-derivation",
            "evaluator": "ag.saga-descent",
            "representation": {
                "invariantId": "saga-descent:residual-derivation",
                "evaluator": "ag.saga-descent"
            },
            "residualDerivation": {
                "derived": true,
                "fault": Value::Null,
                "coverRef": derived.cover_ref,
                "mappedCoverRef": plan.complex.archmap_cover_ref.clone(),
                "derivedComplexRef": plan.id,
                "derivedFrom": ["ArchMap.cover", "ArchMap.contexts.restrictsTo"],
                "lawSurfaceRef": derived.law_surface_ref,
                "charts": plan.complex.charts,
                "edges": derived.edges
            }
        }),
    ];
    let class_certificate = component_cocycle_certificate(plan, &derived.supports);
    // class 語彙は宣言 triple の cocycle パリティを実際に検査した場合だけ解禁する。
    // triple 不在(automatic-c2-zero)は author assertion であり、読みは 1-骨格の
    // 境界所属(boundary 語彙)に留める。
    if let Some(class_certificate) = class_certificate
        .as_ref()
        .filter(|certificate| certificate.certificate_kind == "checked-triple-cocycle-zero")
    {
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
                format!("{ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS}: derived Z1 representative is not in B1")
            } else {
                "derived Z1 representative is zero in Z1/B1".to_string()
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
                    "chartRefs": &class_certificate.component.chart_refs,
                    "overlapRefs": &class_certificate.component.overlap_refs
                },
                "cocycle": {
                    // triple を持つ component だけが実際に検査を走らせる。triple 不在の component は
                    // selected C^2 が零なので cocycle 条件が自動成立する。両者を checked で混ぜない。
                    "checked": class_certificate.certificate_kind == "checked-triple-cocycle-zero",
                    "deltaOne": "zero",
                    "certificateKind": class_certificate.certificate_kind,
                    "tripleOverlapRefs": class_certificate.triple_overlap_refs_json()
                }
            },
            "derivedComplexRef": plan.id,
            "derivedFrom": ["ArchMap.cover", "ArchMap.contexts.restrictsTo"]
        }));
    }
    if let Some(class_certificate) = class_certificate
        .as_ref()
        .filter(|certificate| certificate.certificate_kind == "automatic-c2-zero")
    {
        computed_invariants.push(json!({
            "invariantId": "saga-descent:class-vocabulary-boundary",
            "evaluator": "ag.saga-descent",
            "classVocabulary": {
                "unlocked": false,
                "certificateKind": "automatic-c2-zero",
                "reason": "residual-component-declares-no-triple-overlaps",
                "component": {
                    "chartRefs": &class_certificate.component.chart_refs,
                    "overlapRefs": &class_certificate.component.overlap_refs
                }
            }
        }));
    }
    let assumptions = vec![enumeration_assumption];
    SagaDescentMeasurementV1 {
        structural_verdict,
        computed_invariants,
        assumptions,
    }
}

/// 選択されたArchMapから導出されたSAGA複体の連結成分。
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
            .map(|(id, overlap_refs)| json!({"tripleRef": id, "overlapRefs": overlap_refs}))
            .collect()
    }
}

fn component_cocycle_certificate(
    plan: &DerivedSagaComplexV1,
    supports: &BTreeMap<String, Vec<String>>,
) -> Option<SagaComponentCocycleCertificate> {
    if !plan.complex.enumeration_complete {
        return None;
    }
    if plan
        .complex
        .triple_overlaps
        .iter()
        .map(|triple| triple.id.as_str())
        .collect::<BTreeSet<_>>()
        .len()
        != plan.complex.triple_overlaps.len()
    {
        return None;
    }
    let component = residual_support_component(plan, supports)?;
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
    let component_complex = DerivedSagaComplexDataV1 {
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
    if !saga_complex_has_valid_finite_incidence(&component_complex) {
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
            || !triple_cocycle_is_zero(supports, &triple.overlap_refs)
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

fn residual_support_component(
    plan: &DerivedSagaComplexV1,
    supports: &BTreeMap<String, Vec<String>>,
) -> Option<RepairComplexComponent> {
    let components = repair_complex_components(plan)?;
    let mut component_by_overlap = BTreeMap::new();
    for (component_index, component) in components.iter().enumerate() {
        for overlap_ref in &component.overlap_refs {
            component_by_overlap.insert(overlap_ref.as_str(), component_index);
        }
    }
    let residual_overlap_refs = supports
        .iter()
        .filter(|(_, variables)| !variables.is_empty())
        .map(|(overlap_ref, _)| overlap_ref.as_str())
        .collect::<BTreeSet<_>>();
    if residual_overlap_refs.is_empty() {
        // 零 residual は selected complex 全体で B1 の零境界。class の認証対象は
        // 選択複体そのもの(全 chart / 全 overlap)を単一 scope として取る。
        return Some(RepairComplexComponent {
            chart_refs: plan.complex.charts.clone(),
            overlap_refs: plan
                .complex
                .overlaps
                .iter()
                .map(|overlap| overlap.id.clone())
                .collect(),
        });
    }
    let mut selected_component = None;
    for overlap_ref in residual_overlap_refs {
        let component_index = *component_by_overlap.get(overlap_ref)?;
        if selected_component
            .replace(component_index)
            .is_some_and(|previous| previous != component_index)
        {
            return None;
        }
    }
    selected_component.and_then(|index| components.get(index).cloned())
}

fn repair_complex_components(plan: &DerivedSagaComplexV1) -> Option<Vec<RepairComplexComponent>> {
    let chart_refs = plan.complex.charts.iter().cloned().collect::<BTreeSet<_>>();
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

fn triple_cocycle_is_zero(
    supports: &BTreeMap<String, Vec<String>>,
    overlap_refs: &[String],
) -> bool {
    let mut parity = BTreeMap::<&str, usize>::new();
    for overlap_ref in overlap_refs {
        let Some(variables) = supports.get(overlap_ref.as_str()) else {
            return false;
        };
        for variable in variables {
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

fn solve_boundary_membership(
    plan: &DerivedSagaComplexV1,
    supports: &BTreeMap<String, Vec<String>>,
) -> BoundaryMembershipResult {
    let charts = plan.complex.charts.clone();
    let chart_index = charts
        .iter()
        .enumerate()
        .map(|(index, chart)| (chart.as_str(), index))
        .collect::<BTreeMap<_, _>>();
    let variables = residual_variables(supports);
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
        let support = supports
            .get(overlap.id.as_str())
            .map(|variables| {
                variables
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
        residual_support: residual_support_json(plan, supports),
    }
}

fn residual_variables(supports: &BTreeMap<String, Vec<String>>) -> Vec<String> {
    supports
        .values()
        .flat_map(|variables| variables.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn residual_support_json(
    plan: &DerivedSagaComplexV1,
    supports: &BTreeMap<String, Vec<String>>,
) -> Vec<Value> {
    plan.complex
        .overlaps
        .iter()
        .map(|overlap| {
            json!({
                "overlapRef": overlap.id,
                "support": supports.get(overlap.id.as_str()).cloned().unwrap_or_default()
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

pub(crate) fn solve_f2(mut rows: Vec<Vec<u8>>, unknown_count: usize) -> Option<Vec<u8>> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ArchMapDocumentV2;

    use crate::normalizer::normalize_archmap_v2;

    fn derivation_test_inputs() -> (
        crate::NormalizedArchMapV2,
        crate::MeasurementProfileV1,
        DerivedSagaComplexV1,
        LawEquationSurfaceV1,
    ) {
        let archmap: ArchMapDocumentV2 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/archmap_v2.json"
        ))
        .expect("archmap fixture parses");
        let normalized = normalize_archmap_v2(&archmap, "fixture:archmap_v2");
        let profile: crate::MeasurementProfileV1 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/measurement_profile_ag.json"
        ))
        .expect("profile fixture parses");
        let plan = crate::saga_complex::derive_saga_complex_from_normalized(&normalized, &profile);
        let law_surface: LawEquationSurfaceV1 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/law_surface_ag_v052.json"
        ))
        .expect("law surface fixture parses");
        (normalized, profile, plan, law_surface)
    }

    #[test]
    fn derive_residual_faults_on_overlap_endpoint_outside_charts() {
        let (normalized, profile, mut plan, law_surface) = derivation_test_inputs();
        plan.complex.charts.retain(|chart| chart != "ctx:order");
        let fault = derive_residual(&normalized, &profile, &plan, &law_surface)
            .expect_err("overlap endpoint outside charts must fail closed, not panic");
        assert!(
            fault.contains("must be declared in complex.charts"),
            "fault must name the missing chart declaration: {fault}"
        );
    }

    #[test]
    fn derive_residual_faults_on_duplicate_overlap_id() {
        let (normalized, profile, mut plan, law_surface) = derivation_test_inputs();
        let duplicate_id = plan.complex.overlaps[0].id.clone();
        plan.complex.overlaps[1].id = duplicate_id;
        let fault = derive_residual(&normalized, &profile, &plan, &law_surface).expect_err(
            "duplicate overlap ids must fail closed instead of overwriting residual edges",
        );
        assert!(
            fault.contains("duplicate overlap id"),
            "fault must name the duplicate overlap id: {fault}"
        );
    }

    #[test]
    fn derive_residual_faults_on_duplicate_unordered_pair() {
        let (normalized, profile, mut plan, law_surface) = derivation_test_inputs();
        let mut duplicate = plan.complex.overlaps[0].clone();
        duplicate.id = "overlap:duplicate-pair".to_string();
        std::mem::swap(&mut duplicate.left, &mut duplicate.right);
        plan.complex.overlaps.push(duplicate);
        let fault = derive_residual(&normalized, &profile, &plan, &law_surface)
            .expect_err("duplicate unordered chart pairs must fail closed");
        assert!(
            fault.contains("appears more than once"),
            "fault must name the duplicated pair: {fault}"
        );
    }
}
