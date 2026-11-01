//! 検査済みrelation域の元memberを、通常のAST評価のinstance入力へ戻す。
use super::*;
use crate::observed::public_compare::relation_sources;
impl Environment<'_> {
    pub(in crate::observed) fn recheck_relation_comparison(
        &self,
        graph: &Graph,
        witness: &crate::observed::public_compare::CompareWitness,
    ) -> Result<(), ValidationFailure> {
        crate::observed::public_compare::relations::recheck(graph, witness, &self.control)
    }

    pub(in crate::observed) fn recheck_relation_source(
        &self,
        family: &std::sync::Arc<relation_sources::Family>,
        scalar: Option<&Scalar>,
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        if let Some(value) = scalar {
            data::check(value, self.indexes.inputs.law(), &self.control)?;
        }
        if self
            .results
            .verified::<std::sync::Arc<crate::observed::public_compare::relation_sources::Family>>()
            .iter()
            .any(|known| std::sync::Arc::ptr_eq(known, family))
        {
            return Ok(());
        }
        family
            .table
            .recheck(self.indexes.inputs, &self.control)
            .map_err(|f| f.cause)?;
        self.tick()?;
        self.results.remember(family.clone());
        Ok(())
    }
    pub(in crate::observed::environment) fn instance_source_declaration(
        &self,
        graph: &Graph,
        index: usize,
    ) -> Result<Option<String>, ValidationFailure> {
        if let Some(declaration) =
            crate::observed::object_reading_evaluation::declaration(graph, index)?
        {
            return Ok(Some(declaration));
        }
        if let Some(declaration) = crate::observed::law_evaluation::declaration(graph, index)? {
            return Ok(Some(declaration));
        }
        relation_sources::instance_declaration(graph, index)
    }
    pub(in crate::observed::environment) fn relation_source_inputs(
        &self,
        graph: &Graph,
        index: usize,
    ) -> Result<Option<super::super::FrameInputs>, ValidationFailure> {
        self.tick()?;
        if relation_sources::instance_declaration(graph, index)?.is_none() {
            return Ok(None);
        }
        let record = graph
            .instances
            .get(index)
            .ok_or("relationの元instanceがない")?;
        let limit = self.state.cutoff.get().min(graph.nodes.len());
        for r in [record.source, record.domain, record.member] {
            if r.0 >= limit {
                return Err("relation instanceが未出の元域を参照した".into());
            }
            self.validate_at(graph, graph.get(r)?, r.0)?;
        }
        let Some(inputs) = relation_sources::instance_bindings(self, graph, index, limit)? else {
            return Err("relationの元域が変わった".into());
        };
        let mut variables = BTreeMap::new();
        for binding in &inputs.bindings {
            self.tick()?;
            self.validate_at(graph, graph.get(binding.value)?, binding.value.0)?;
            let scalar = graph.scalar(binding.value)?.clone();
            if scalar.ty() != binding.ty {
                return Err("relation instanceの元parameter型が違う".into());
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
                    scope: inputs.base.clone(),
                    known_value: Some(scalar),
                    support: graph.get(binding.value)?.support.clone(),
                    scalar_scope: Some(graph.get(binding.value)?.scope.clone()),
                },
            );
        }
        Ok(Some((inputs.bindings, variables, inputs.base)))
    }
}
