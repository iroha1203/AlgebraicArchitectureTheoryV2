//! 完全束縛済みnative Law行の元値と対象を、通常Sourceの再検査へ渡す。
use super::*;
use crate::observed::{
    construction_result::{ConstructionData as D, ConstructionValue},
    law_evaluation as frames,
};
impl Environment<'_> {
    pub(in crate::observed) fn recheck_law_evaluation_inputs(
        &self,
        graph: &Graph,
        origin: NodeRef,
        architecture: NodeRef,
    ) -> Result<(), ValidationFailure> {
        for r in [origin, architecture] {
            self.tick()?;
            self.validate_at(graph, graph.get(r)?, r.0)?;
        }
        Ok(())
    }

    pub(in crate::observed) fn instance_evaluation_bindings(
        &self,
        graph: &Graph,
        index: usize,
    ) -> Result<(Vec<Binding>, Scope), ValidationFailure> {
        let (bindings, _, scope) = self.family_instance_inputs(graph, index)?;
        Ok((bindings, scope))
    }
    pub(super) fn native_law_source_allowed(
        &self,
        graph: &Graph,
        index: usize,
        span: (usize, usize),
    ) -> Result<bool, ValidationFailure> {
        let (allowed, guard) =
            frames::body_guard(graph, index, span, self.cutoff.get().min(graph.nodes.len()))?;
        if let Some(guard) = guard {
            self.validate_at(graph, graph.get(guard)?, guard.0)?;
            let Some(Payload::Evaluation { value, .. }) = &graph.get(guard)?.payload else {
                return Err("元Law guardの通常評価がない".into());
            };
            return Ok(allowed && graph.boolean(*value)? != Some(false));
        }
        Ok(allowed)
    }
    pub(super) fn recheck_law_frame(
        &self,
        graph: &Graph,
        value: &ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        let D::LawFrame(data) = &value.data else {
            return Ok(());
        };
        for r in [data.origin, data.architecture] {
            self.tick()?;
            self.validate_at(graph, graph.get(r)?, r.0)?;
        }
        for r in data.arguments() {
            self.validate_at(graph, graph.get(r)?, r.0)?;
        }
        Ok(())
    }
    pub(super) fn native_law_source_inputs(
        &self,
        graph: &Graph,
        index: usize,
    ) -> Result<Option<FrameInputs>, ValidationFailure> {
        self.tick()?;
        let limit = self.cutoff.get().min(graph.nodes.len());
        let Some(inputs) = frames::instance_inputs(graph, index, limit)? else {
            return Ok(None);
        };
        let record = graph.instances.get(index).ok_or("元Law instanceがない")?;
        for r in [
            record.source,
            record.domain,
            record.member,
            inputs.architecture,
        ] {
            self.validate_at(graph, graph.get(r)?, r.0)?;
        }
        let mut variables = BTreeMap::new();
        for binding in &inputs.bindings {
            self.tick()?;
            self.validate_at(graph, graph.get(binding.value)?, binding.value.0)?;
            let scalar = graph.scalar(binding.value)?.clone();
            if scalar.ty() != binding.ty {
                return Err("native Lawの元parameter型が違う".into());
            }
            variables.insert(
                binding.name.clone(),
                SourceValue {
                    condition_failed: false,
                    condition_pending: false,
                    symbolic: None,
                    comparison: None,
                    affine: crate::observed::affine::constant(&scalar, &self.control)?
                        .map(Box::new),
                    scope: inputs.origin.scope.clone(),
                    known_value: Some(scalar),
                    support: graph.get(binding.value)?.support.clone(),
                    scalar_scope: Some(graph.get(binding.value)?.scope.clone()),
                },
            );
        }
        Ok(Some((inputs.bindings, variables, inputs.origin.scope)))
    }
}
