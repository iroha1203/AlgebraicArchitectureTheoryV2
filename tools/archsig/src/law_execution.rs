use std::collections::{BTreeMap, BTreeSet};

use crate::{LawEquationSurfaceV1, LawQuotientSheafConditionV1, NormalizedArchMapV2};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DerivedGroundingSkeletonV1 {
    pub(crate) simplex: String,
    pub(crate) support_atom_ref: String,
    pub(crate) required_law_id: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DerivedGroundingDefectSourceV1 {
    pub(crate) law_id: String,
    pub(crate) cover_ref: String,
    pub(crate) chart_defects: Vec<DerivedGroundingChartDefectV1>,
    pub(crate) holds_criterion: DerivedGroundingHoldsCriterionV1,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DerivedGroundingChartDefectV1 {
    pub(crate) chart: String,
    pub(crate) defect_observable: DerivedGroundingDefectObservableV1,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DerivedGroundingDefectObservableV1 {
    pub(crate) axis: String,
    pub(crate) predicate: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DerivedGroundingHoldsCriterionV1 {
    pub(crate) kind: String,
    pub(crate) zero_sense: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LawExecutionPlanV1 {
    pub(crate) surface_id: String,
    pub(crate) evaluator: String,
    pub(crate) evaluator_law_ids: BTreeSet<String>,
    pub(crate) selected_law_id: String,
    pub(crate) section_witness_variables: Option<Vec<String>>,
    pub(crate) section_variable_aliases: Option<BTreeMap<String, String>>,
    pub(crate) section_forbidden_supports: Option<Vec<Vec<String>>>,
    pub(crate) grounded_variable_aliases: Option<BTreeMap<String, String>>,
    pub(crate) grounded_forbidden_supports: Option<Vec<Vec<String>>>,
    pub(crate) grounded_skeleton: Option<Vec<DerivedGroundingSkeletonV1>>,
    pub(crate) grounded_defect_source: Option<DerivedGroundingDefectSourceV1>,
    pub(crate) stage3_quotient_sheaf_condition: Option<LawQuotientSheafConditionV1>,
}

fn derive_grounded_contract(
    normalized: &NormalizedArchMapV2,
    profile: &crate::MeasurementProfileV1,
    law_id: &str,
) -> (
    Vec<DerivedGroundingSkeletonV1>,
    DerivedGroundingDefectSourceV1,
) {
    let charts = normalized
        .covers
        .iter()
        .find(|cover| {
            cover.normalized_cover_id == profile.cover_ref
                || cover.source_cover_id == profile.cover_ref
        })
        .map(|cover| cover.context_ids.clone())
        .unwrap_or_default();
    let chart_set = charts.iter().collect::<BTreeSet<_>>();
    let skeleton = normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "cech"
                && atom.predicate == "sectionValue"
                && atom
                    .context_memberships
                    .iter()
                    .any(|context| chart_set.contains(context))
        })
        .map(|atom| DerivedGroundingSkeletonV1 {
            simplex: format!("vertex:{}", atom.normalized_atom_id),
            support_atom_ref: atom.normalized_atom_id.clone(),
            required_law_id: law_id.to_string(),
        })
        .collect();
    let chart_defects = charts
        .iter()
        .map(|chart| DerivedGroundingChartDefectV1 {
            chart: (*chart).clone(),
            defect_observable: DerivedGroundingDefectObservableV1 {
                axis: "square-free".to_string(),
                predicate: "support".to_string(),
            },
        })
        .collect();
    (
        skeleton,
        DerivedGroundingDefectSourceV1 {
            law_id: law_id.to_string(),
            cover_ref: profile.cover_ref.clone(),
            chart_defects,
            holds_criterion: DerivedGroundingHoldsCriterionV1 {
                kind: "defect-raw-value-zero".to_string(),
                zero_sense: "empty-witness-set".to_string(),
            },
        },
    )
}

pub(crate) fn build_law_execution_plan(
    normalized: &NormalizedArchMapV2,
    surface: Option<&LawEquationSurfaceV1>,
    policy_law_id: Option<&str>,
    evaluator: &str,
    profile: &crate::MeasurementProfileV1,
) -> Result<Option<LawExecutionPlanV1>, String> {
    let Some(surface) = surface else {
        return if matches!(
            evaluator,
            "ag.cech-obstruction" | "ag.section-factorization"
        ) {
            Err(format!(
                "{evaluator} requires --law-surface; no registry or MeasurementProfile fallback is permitted"
            ))
        } else {
            Ok(None)
        };
    };
    let selected_law = if let Some(policy_law_id) = policy_law_id {
        let selected_law = surface.laws.iter().find(|law| law.law_id == policy_law_id);
        let Some(selected_law) = selected_law else {
            return if matches!(
                evaluator,
                "ag.cech-obstruction" | "ag.section-factorization"
            ) {
                Err(format!(
                    "{evaluator} law {policy_law_id} is not declared by supplied law surface {}",
                    surface.id
                ))
            } else {
                Ok(None)
            };
        };
        selected_law
    } else {
        let selected_law = surface
            .laws
            .iter()
            .find(|law| law.evaluator_ref.as_deref() == Some(evaluator));
        let Some(selected_law) = selected_law else {
            return if matches!(
                evaluator,
                "ag.cech-obstruction" | "ag.section-factorization"
            ) {
                Err(format!(
                    "{evaluator} requires a policy law or evaluatorRef declaration in supplied law surface {}",
                    surface.id
                ))
            } else {
                Ok(None)
            };
        };
        selected_law
    };
    if selected_law
        .evaluator_ref
        .as_deref()
        .is_some_and(|evaluator_ref| evaluator_ref != evaluator)
    {
        return Err(format!(
            "{evaluator} policy law {} has evaluatorRef mismatch",
            selected_law.law_id
        ));
    }
    let evaluator_law_ids = BTreeSet::from([selected_law.law_id.clone()]);
    let mut section_witness_variables = Vec::new();
    let mut section_variable_aliases = BTreeMap::new();
    for witness in &selected_law.witness_variables {
        let axis = witness.binding.axis.as_deref().unwrap_or_default();
        match evaluator {
            "ag.cech-obstruction" => {
                if axis != "cech" || witness.binding.predicate.as_deref() != Some("sectionValue") {
                    return Err(format!(
                        "{evaluator} law {} witness {} has an unsupported binding",
                        selected_law.law_id, witness.variable
                    ));
                }
            }
            "ag.section-factorization" => {
                if axis != "section-factorization"
                    || !matches!(
                        witness.binding.predicate.as_deref(),
                        Some("support" | "cooccurrence")
                    )
                {
                    return Err(format!(
                        "{evaluator} law {} witness {} has an unsupported binding",
                        selected_law.law_id, witness.variable
                    ));
                }
                let alias = witness
                    .binding
                    .archmap_variable
                    .clone()
                    .unwrap_or_else(|| witness.variable.clone());
                section_variable_aliases.insert(witness.variable.clone(), alias.clone());
                section_witness_variables.push(alias);
            }
            _ => {}
        }
    }
    section_witness_variables.sort();
    section_witness_variables.dedup();
    let section_forbidden_supports = if evaluator == "ag.section-factorization" {
        if section_witness_variables.is_empty()
            || selected_law.forbidden_support_generators.is_empty()
        {
            return Err(format!(
                "{evaluator} law {} must declare witnessVariables and forbiddenSupportGenerators",
                selected_law.law_id
            ));
        }
        Some(
            selected_law
                .forbidden_support_generators
                .iter()
                .map(|generator| generator.support.clone())
                .collect(),
        )
    } else {
        None
    };
    let (grounded_variable_aliases, grounded_forbidden_supports) = if evaluator
        == "ag.saga-grounded"
    {
        let mut aliases = BTreeMap::new();
        for witness in &selected_law.witness_variables {
            let alias = witness
                .binding
                .archmap_variable
                .clone()
                .unwrap_or_else(|| witness.variable.clone());
            if aliases.insert(witness.variable.clone(), alias).is_some() {
                return Err(format!(
                    "{evaluator} law {} contains duplicate witness variable {}",
                    selected_law.law_id, witness.variable
                ));
            }
        }
        if aliases.is_empty() || selected_law.forbidden_support_generators.is_empty() {
            return Err(format!(
                "{evaluator} law {} must declare witnessVariables and forbiddenSupportGenerators",
                selected_law.law_id
            ));
        }
        let supports = selected_law
            .forbidden_support_generators
            .iter()
            .map(|generator| {
                if generator.support.is_empty()
                    || generator
                        .support
                        .iter()
                        .any(|variable| !aliases.contains_key(variable))
                {
                    return Err(format!(
                        "{evaluator} law {} has forbidden support outside witnessVariables",
                        selected_law.law_id
                    ));
                }
                Ok(generator.support.clone())
            })
            .collect::<Result<Vec<_>, _>>()?;
        (Some(aliases), Some(supports))
    } else {
        (None, None)
    };
    let (grounded_skeleton, grounded_defect_source) = if evaluator == "ag.saga-grounded" {
        let (skeleton, source) =
            derive_grounded_contract(normalized, profile, &selected_law.law_id);
        (Some(skeleton), Some(source))
    } else {
        (None, None)
    };
    Ok(Some(LawExecutionPlanV1 {
        surface_id: surface.id.clone(),
        evaluator: evaluator.to_string(),
        evaluator_law_ids,
        selected_law_id: selected_law.law_id.clone(),
        section_witness_variables: (!section_witness_variables.is_empty())
            .then_some(section_witness_variables),
        section_variable_aliases: (!section_variable_aliases.is_empty())
            .then_some(section_variable_aliases),
        section_forbidden_supports,
        grounded_variable_aliases,
        grounded_forbidden_supports,
        grounded_skeleton,
        grounded_defect_source,
        stage3_quotient_sheaf_condition: surface.quotient_sheaf_condition.clone(),
    }))
}
