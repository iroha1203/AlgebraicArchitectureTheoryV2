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
}
/// 依存producerの再検査中に別の根を選んでも、呼出し側の環境を復元する。
pub(in crate::observed) struct ArchitectureGuard<'e, 'i> {
    environment: &'e Environment<'i>,
    previous: Option<ArchitectureContext>,
}
impl Drop for ArchitectureGuard<'_, '_> {
    fn drop(&mut self) {
        self.environment.architecture.replace(self.previous.take());
    }
}
impl<'i> Environment<'i> {
    pub(in crate::observed) fn architecture_ref(&self) -> Option<NodeRef> {
        self.architecture.borrow().as_ref().map(|c| c.reference)
    }
    pub(super) fn object_domain(&self) -> Option<Arc<ObjectDomain>> {
        self.architecture
            .borrow()
            .as_ref()
            .map(|c| Arc::clone(&c.domain))
            .or_else(|| self.object.clone())
    }
    pub(in crate::observed) fn enter_architecture(
        &self,
        graph: &Graph,
    ) -> Result<ArchitectureGuard<'_, 'i>, ValidationFailure> {
        let context = self.current_context(graph);
        let selected = (|| {
            let Some(request) = self
                .original_requests
                .and_then(|rs| rs.get(context.request))
            else {
                return Ok(None);
            };
            if !graph.requests.is_empty() && graph.requests.get(context.request) != Some(request) {
                return Err("環境選択のRequestが元入力と違う".into());
            }
            if !matches!(request.kind, QuestionKind::Evaluate | QuestionKind::Check) {
                return Ok(None);
            }
            let Some(argument) = request.arguments.iter().find(|a| a.name == "on") else {
                return Ok(None);
            };
            #[cfg(test)]
            crate::observed::data::observe_actual((0, 0), context, "architecture_environment", 0);
            self.control
                .clone()
                .checkpoint(Checkpoint::ObjectEvaluation)?;
            let reference = match self.answer_binding(graph, &argument.value, (0, 0)) {
                Ok(AnswerBinding::Reference(r)) => r,
                Ok(AnswerBinding::Inapplicable(_))
                | Err(ValidationFailure::UnsupportedExpression { .. }) => return Ok(None),
                Ok(AnswerBinding::Projection(_)) => return Ok(None),
                Err(failure) => return Err(failure),
            };
            if reference.0 >= self.cutoff.get() {
                return Err("環境が未出のArchitectureを参照した".into());
            }
            let node = graph.get(reference)?;
            let Some(Payload::Construction(value)) = &node.payload else {
                return Ok(None);
            };
            if value.is_blocked() {
                return Ok(None);
            }
            if !matches!(value.data, ConstructionData::Architecture { .. })
                || node.ty != NodeType::Construction(ConstructionType::Architecture)
            {
                return Ok(None);
            }
            self.validate_at(graph, node, reference.0)?;
            let Witness::Architecture(witness) = &value.witness else {
                return Err("環境Architectureの元構成がない".into());
            };
            let domain =
                ObjectDomain::from_readings(self.inputs, witness.readings(), 0, &self.control)?;
            self.tick()?;
            Ok(Some(ArchitectureContext {
                reference,
                domain: Arc::new(domain),
            }))
        })()?;
        Ok(ArchitectureGuard {
            environment: self,
            previous: self.architecture.replace(selected),
        })
    }
    pub(super) fn validate_evaluation_environment(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        if let Some(Payload::Evaluation { environment, .. }) = &node.payload {
            if *environment != self.architecture_ref() {
                return Err("評価の環境Refが元Requestのonと違う".into());
            }
            if let Some(r) = environment {
                if r.0 >= limit {
                    return Err("評価の環境が既出Architectureでない".into());
                }
                self.validate_at(graph, graph.get(*r)?, r.0)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "architecture_environment_tests.rs"]
mod tests;
