//! 公開Architectureの元導出を照合し、現在のRequestだけの参照域を選ぶ。
use super::*;
use crate::observed::{
    construction_result::{ConstructionData, ConstructionType, Witness},
    object_evaluate::ObjectDomain,
};
use std::sync::Arc;

#[derive(Clone)]
pub(super) struct ArchitectureContext {
    reference: NodeRef,
    domain: Arc<ObjectDomain>,
    scope: Scope,
    overrides: BTreeMap<Fact, (NodeRef, Scalar, Scope)>,
}
/// 依存producerの再検査中に別の根を選んでも、呼出し側の環境を復元する。
pub(in crate::observed) struct ArchitectureGuard<'e, 'i> {
    environment: &'e Environment<'i>,
    previous: Option<ArchitectureContext>,
}
impl Drop for ArchitectureGuard<'_, '_> {
    fn drop(&mut self) {
        self.environment
            .state
            .architecture
            .replace(self.previous.take());
    }
}
impl<'i> Environment<'i> {
    pub(super) fn object_domain(&self) -> Option<Arc<ObjectDomain>> {
        self.state
            .architecture
            .borrow()
            .as_ref()
            .map(|c| Arc::clone(&c.domain))
            .or_else(|| self.indexes.object.clone())
    }
    pub(in crate::observed) fn enter_architecture(
        &self,
        graph: &Graph,
    ) -> Result<ArchitectureGuard<'_, 'i>, ValidationFailure> {
        let context = self.current_context(graph);
        let selected = (|| {
            if let Some(index) = context.instance {
                if let Some(reference) = crate::observed::object_reading_evaluation::architecture(
                    graph,
                    index,
                    self.state.cutoff.get().min(graph.nodes.len()),
                )? {
                    return self.select_architecture(graph, reference);
                }
                if let Some(reference) = crate::observed::law_evaluation::architecture(
                    graph,
                    index,
                    self.state.cutoff.get().min(graph.nodes.len()),
                )? {
                    return self.select_architecture(graph, reference);
                }
            }
            let Some(request) = self
                .indexes
                .original_requests
                .and_then(|rs| rs.get(context.request))
            else {
                return Ok(None);
            };
            if !graph.requests.is_empty() && graph.requests.get(context.request) != Some(request) {
                return Err(internal!("環境選択のRequestが元入力と違う").into());
            }
            if !matches!(
                request.kind,
                QuestionKind::Evaluate
                    | QuestionKind::Check
                    | QuestionKind::Solve
                    | QuestionKind::Repair
            ) {
                return Ok(None);
            }
            let Some(argument) = request.arguments.iter().find(|a| a.name == "on") else {
                return Ok(None);
            };
            if matches!(argument.value, Selector::Subject { .. }) {
                return Ok(None);
            }
            #[cfg(test)]
            crate::observed::data::observe_actual((0, 0), context, "architecture_environment", 0);
            self.control.checkpoint(Checkpoint::ObjectEvaluation)?;
            let reference = match self.answer_binding(graph, &argument.value, (0, 0)) {
                Ok(AnswerBinding::Reference(r)) => r,
                Ok(AnswerBinding::Inapplicable(_))
                | Err(ValidationFailure::UnsupportedExpression { .. }) => return Ok(None),
                Ok(AnswerBinding::Projection(_)) => return Ok(None),
                Err(failure) => return Err(failure),
            };
            self.select_architecture(graph, reference)
        })()?;
        Ok(ArchitectureGuard {
            environment: self,
            previous: self.state.architecture.replace(selected),
        })
    }
    pub(super) fn select_architecture(
        &self,
        graph: &Graph,
        reference: NodeRef,
    ) -> Result<Option<ArchitectureContext>, ValidationFailure> {
        if reference.0 >= self.state.cutoff.get() {
            return Err(internal!("環境が未出のArchitectureを参照した").into());
        }
        let node = graph.get(reference)?;
        let Some(Payload::Construction(value)) = &node.payload else {
            return Ok(None);
        };
        if value.is_blocked() || node.ty != NodeType::Construction(ConstructionType::Architecture) {
            return Ok(None);
        }
        if !matches!(
            value.data,
            ConstructionData::Architecture { .. }
                | ConstructionData::ObjectComponents(_)
                | ConstructionData::Change(_)
                | ConstructionData::Quotient(_)
        ) {
            return Ok(None);
        }
        self.validate_at(graph, node, reference.0)?;
        let Witness::Architecture(witness) = &value.witness else {
            return Err(internal!("環境Architectureの元構成がない").into());
        };
        let object = match &value.data {
            ConstructionData::Architecture { .. }
            | ConstructionData::Change(_)
            | ConstructionData::Quotient(_) => 0,
            ConstructionData::ObjectComponents(data) => data.architecture_object(reference)?,
            _ => return Err(internal!("環境Architectureの構成が違う").into()),
        };
        let domain = ObjectDomain::from_readings(
            self.indexes.inputs,
            witness.readings(),
            object,
            &self.control,
        )?;
        self.tick()?;
        Ok(Some(ArchitectureContext {
            reference,
            domain: Arc::new(domain),
            scope: node.scope.clone(),
            overrides: match &value.data {
                ConstructionData::Change(d) => d
                    .overrides(graph)?
                    .into_iter()
                    .map(|(f, r, v)| Ok((f, (r, v, graph.get(r)?.scope.clone()))))
                    .collect::<Result<_, ValidationFailure>>()?,
                ConstructionData::Quotient(d) => d
                    .overrides(graph)?
                    .into_iter()
                    .map(|(f, r, v)| Ok((f, (r, v, graph.get(r)?.scope.clone()))))
                    .collect::<Result<_, ValidationFailure>>()?,
                _ => BTreeMap::new(),
            },
        }))
    }
    pub(super) fn validate_evaluation_environment(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        if let Some(Payload::Evaluation { environment, .. }) = &node.payload {
            if *environment != self.state.architecture_ref() {
                return Err(internal!("評価の環境Refが元Requestのonと違う").into());
            }
            if let Some(r) = environment {
                if r.0 >= limit {
                    return Err(internal!("評価の環境が既出Architectureでない").into());
                }
                self.validate_at(graph, graph.get(*r)?, r.0)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;

impl EvaluationState {
    pub(in crate::observed) fn architecture_ref(&self) -> Option<NodeRef> {
        self.architecture.borrow().as_ref().map(|c| c.reference)
    }
    pub(in crate::observed) fn architecture_value(&self, fact: &Fact) -> Option<(NodeRef, Scalar)> {
        self.architecture
            .borrow()
            .as_ref()?
            .overrides
            .get(fact)
            .map(|(r, v, _)| (*r, v.clone()))
    }
    pub(in crate::observed) fn architecture_scalar_scope(&self, fact: &Fact) -> Option<Scope> {
        self.architecture
            .borrow()
            .as_ref()?
            .overrides
            .get(fact)
            .map(|(_, _, s)| s.clone())
    }
    pub(super) fn architecture_has_value(&self, reference: NodeRef) -> bool {
        self.architecture
            .borrow()
            .as_ref()
            .is_some_and(|a| a.overrides.values().any(|(r, _, _)| *r == reference))
    }
    pub(in crate::observed) fn architecture_values(&self) -> Vec<(Fact, Scalar)> {
        self.architecture
            .borrow()
            .as_ref()
            .map(|a| {
                a.overrides
                    .iter()
                    .map(|(f, (_, v, _))| (f.clone(), v.clone()))
                    .collect()
            })
            .unwrap_or_default()
    }
    pub(in crate::observed) fn architecture_scope(&self) -> Scope {
        self.architecture
            .borrow()
            .as_ref()
            .map(|c| c.scope.clone())
            .unwrap_or_default()
    }
}
