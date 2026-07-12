use std::collections::BTreeSet;

use crate::{LawEquationSurfaceV1, NormalizedArchMapV2};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LawExecutionPlanV1 {
    pub(crate) surface_id: String,
    pub(crate) evaluator: String,
    pub(crate) evaluator_law_ids: BTreeSet<String>,
    pub(crate) selected_law_id: String,
    pub(crate) cech_edges: Option<BTreeSet<[String; 2]>>,
    pub(crate) section_witness_variables: Option<Vec<String>>,
    pub(crate) section_forbidden_supports: Option<Vec<Vec<String>>>,
}

pub(crate) fn build_law_execution_plan(
    normalized: &NormalizedArchMapV2,
    surface: Option<&LawEquationSurfaceV1>,
    policy_law_id: Option<&str>,
    evaluator: &str,
    selected_contexts: Option<&BTreeSet<String>>,
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
        let selected_law = surface
            .laws
            .iter()
            .find(|law| law.law_id == policy_law_id)
            .or_else(|| {
                (policy_law_id == evaluator)
                    .then(|| {
                        surface
                            .laws
                            .iter()
                            .find(|law| law.evaluator_ref.as_deref() == Some(evaluator))
                    })
                    .flatten()
            });
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
    let derived_edges = normalized
        .contexts
        .iter()
        .filter(|context| {
            selected_contexts
                .is_none_or(|contexts| contexts.contains(&context.normalized_context_id))
        })
        .flat_map(|context| {
            context
                .restricts_to
                .iter()
                .filter(move |target| {
                    normalized
                        .contexts
                        .iter()
                        .any(|candidate| candidate.normalized_context_id == **target)
                        && selected_contexts.is_none_or(|contexts| contexts.contains(*target))
                })
                .map(|target| {
                    let mut edge = [context.normalized_context_id.clone(), target.clone()];
                    edge.sort();
                    edge
                })
        })
        .collect::<BTreeSet<_>>();

    let mut explicit_cech_edges = BTreeSet::new();
    let mut section_witness_variables = Vec::new();
    for witness in &selected_law.witness_variables {
        let axis = witness.binding.axis.as_deref().unwrap_or_default();
        match evaluator {
            "ag.cech-obstruction" => {
                if axis != "cech" {
                    return Err(format!(
                        "{evaluator} law {} witness {} has binding axis {axis}, expected cech",
                        selected_law.law_id, witness.variable
                    ));
                }
                let edge = witness.binding.edge.as_ref().ok_or_else(|| {
                    format!(
                        "law {} cech witness {} has no edge binding",
                        selected_law.law_id, witness.variable
                    )
                })?;
                if edge.len() != 2 {
                    return Err(format!(
                        "law {} cech witness {} edge binding must contain two context refs",
                        selected_law.law_id, witness.variable
                    ));
                }
                let mut pair = [edge[0].clone(), edge[1].clone()];
                pair.sort();
                if !derived_edges.contains(&pair) {
                    return Err(format!(
                        "law {} cech witness {} edge {} -> {} is not in the selected restriction 1-skeleton",
                        selected_law.law_id, witness.variable, edge[0], edge[1]
                    ));
                }
                explicit_cech_edges.insert(pair);
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
                section_witness_variables.push(
                    witness
                        .binding
                        .archmap_variable
                        .clone()
                        .unwrap_or_else(|| witness.variable.clone()),
                );
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
    Ok(Some(LawExecutionPlanV1 {
        surface_id: surface.id.clone(),
        evaluator: evaluator.to_string(),
        evaluator_law_ids,
        selected_law_id: selected_law.law_id.clone(),
        cech_edges: (!explicit_cech_edges.is_empty()).then_some(explicit_cech_edges),
        section_witness_variables: (!section_witness_variables.is_empty())
            .then_some(section_witness_variables),
        section_forbidden_supports,
    }))
}
