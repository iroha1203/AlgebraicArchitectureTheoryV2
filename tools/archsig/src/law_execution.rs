use std::collections::BTreeSet;

use crate::{LawEquationSurfaceV1, NormalizedArchMapV2};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LawExecutionPlanV1 {
    pub(crate) surface_id: String,
    pub(crate) evaluator: String,
    pub(crate) evaluator_law_ids: BTreeSet<String>,
    pub(crate) cech_edges: Option<BTreeSet<[String; 2]>>,
}

pub(crate) fn build_law_execution_plan(
    normalized: &NormalizedArchMapV2,
    surface: Option<&LawEquationSurfaceV1>,
    policy_law_id: Option<&str>,
    evaluator: &str,
) -> Result<Option<LawExecutionPlanV1>, String> {
    let Some(surface) = surface else {
        return Ok(None);
    };
    let evaluator_law_ids = surface
        .laws
        .iter()
        .filter(|law| {
            law.evaluator_ref.as_deref() == Some(evaluator)
                || policy_law_id.is_some_and(|law_id| law.law_id == law_id)
        })
        .map(|law| law.law_id.clone())
        .collect::<BTreeSet<_>>();
    if evaluator_law_ids.is_empty() {
        return Ok(None);
    }
    let derived_edges = normalized
        .contexts
        .iter()
        .flat_map(|context| {
            context
                .restricts_to
                .iter()
                .filter(move |target| {
                    normalized
                        .contexts
                        .iter()
                        .any(|candidate| candidate.normalized_context_id == **target)
                })
                .map(|target| {
                    let mut edge = [context.normalized_context_id.clone(), target.clone()];
                    edge.sort();
                    edge
                })
        })
        .collect::<BTreeSet<_>>();
    let mut explicit_cech_edges = BTreeSet::new();
    for law in surface.laws.iter().filter(|law| {
        law.evaluator_ref.as_deref() == Some(evaluator)
            || policy_law_id.is_some_and(|law_id| law.law_id == law_id)
    }) {
        for witness in &law.witness_variables {
            if witness.binding.axis.as_deref() != Some("cech") {
                continue;
            }
            let edge = witness.binding.edge.as_ref().ok_or_else(|| {
                format!(
                    "law {} cech witness {} has no edge binding",
                    law.law_id, witness.variable
                )
            })?;
            if edge.len() != 2 {
                return Err(format!(
                    "law {} cech witness {} edge binding must contain two context refs",
                    law.law_id, witness.variable
                ));
            }
            let mut pair = [edge[0].clone(), edge[1].clone()];
            pair.sort();
            if !derived_edges.contains(&pair) {
                return Err(format!(
                    "law {} cech witness {} edge {} -> {} is not in the derived restriction 1-skeleton",
                    law.law_id, witness.variable, edge[0], edge[1]
                ));
            }
            explicit_cech_edges.insert(pair);
        }
    }
    Ok(Some(LawExecutionPlanV1 {
        surface_id: surface.id.clone(),
        evaluator: evaluator.to_string(),
        evaluator_law_ids,
        cech_edges: (!explicit_cech_edges.is_empty()).then_some(explicit_cech_edges),
    }))
}
