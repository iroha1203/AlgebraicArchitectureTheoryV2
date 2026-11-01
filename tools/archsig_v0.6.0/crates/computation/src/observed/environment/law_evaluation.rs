//! native Law行の固定値・未束縛数値parameter・対象を通常Sourceの再検査へ渡す。
use super::*;
use crate::observed::law_evaluation as frames;
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
        // 全域関数のSourceは通常のguard評価より先に構成される。
        // guardが全域で真、または正確な適用fiberと型付き残差の全域表示を持つ
        // 場合に、その本文を構成できる。後者はguardの真偽を確定しない。固定Architectureの読取りはこの全域計算の
        // 入力であり、未観測値や一つのparameter代入を真として補完しない。
        if let Some(inputs) =
            frames::instance_inputs(graph, index, self.state.cutoff.get().min(graph.nodes.len()))?
            && let Some(guard) = inputs.origin.guard
        {
            let law = self.indexes.inputs.law();
            let body = law
                .exprs()
                .get(inputs.origin.body)
                .ok_or("元Law body式がない")?
                .span;
            let guard_span = law.exprs().get(guard).ok_or("元Law guard式がない")?.span;
            if body.0 <= span.0 && span.1 <= body.1 {
                if !inputs.origin.body_allowed {
                    return Ok(false);
                }
                let request = graph
                    .requests
                    .get(self.current_context(graph).request)
                    .ok_or("元Law要求がない")?;
                if let Some(plan) = self.universal_family_plan(graph, request, &inputs.bindings)?
                    && plan.guard == Some(guard)
                    && !plan.parameters.is_empty()
                    && plan
                        .parameters
                        .iter()
                        .all(|p| numeric_parameters::numeric_width(&p.ty).is_some())
                {
                    let guard = self.universal_template_source_analysis(
                        graph,
                        &plan,
                        guard_span,
                        &inputs.bindings,
                    )?;
                    if guard.analysis.known_value == Some(Scalar::Bool(true))
                        || inputs.origin.zero_residual
                        || inputs.origin.guarded_family
                    {
                        return Ok(true);
                    }
                }
            }
        }
        let (allowed, guard) = frames::body_guard(
            graph,
            index,
            span,
            self.state.cutoff.get().min(graph.nodes.len()),
        )?;
        if let Some(guard) = guard {
            self.validate_at(graph, graph.get(guard)?, guard.0)?;
            let Some(Payload::Evaluation { value, .. }) = &graph.get(guard)?.payload else {
                return Err("元Law guardの通常評価がない".into());
            };
            return Ok(allowed && graph.boolean(*value)? != Some(false));
        }
        Ok(allowed)
    }
    pub(in crate::observed) fn require_native_law_expression(
        &self,
        graph: &Graph,
        expression: usize,
    ) -> Result<(), ValidationFailure> {
        if let Some(index) = self.current_context(graph).instance {
            let span = self
                .indexes
                .inputs
                .law()
                .exprs()
                .get(expression)
                .ok_or("元Law式IDがない")?
                .span;
            if !self.native_law_source_allowed(graph, index, span)? {
                return Err("非適用native Lawのbodyは評価できない".into());
            }
        }
        Ok(())
    }
    pub(super) fn native_law_skipped_source(
        &self,
        graph: &Graph,
        index: usize,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<Option<SourceAnalysis>, ValidationFailure> {
        let Some(inputs) =
            frames::instance_inputs(graph, index, self.state.cutoff.get().min(graph.nodes.len()))?
        else {
            return Ok(None);
        };
        let context = self.current_context(graph);
        if context.frame.is_some()
            || context.iteration.is_some()
            || context.case.is_some()
            || inputs.bindings != bindings
            || inputs.origin.body_allowed
            || self
                .indexes
                .inputs
                .law()
                .exprs()
                .get(inputs.origin.body)
                .ok_or("元body式IDがない")?
                .span
                != span
        {
            return Ok(None);
        }
        let request = graph
            .requests
            .get(context.request)
            .ok_or("元Law要求がない")?;
        let universal_false = if let Some(plan) =
            self.universal_family_plan(graph, request, bindings)?
            && plan
                .parameters
                .iter()
                .all(|p| numeric_parameters::numeric_width(&p.ty).is_some())
            && let Some(guard) = plan.guard
        {
            // 全域templateのSourceは実guard評価より先に保持される。元guardを
            // 全parameter上で再計算し、falseの場合だけ値のないbodyを保持する。
            let guard = self.universal_template_source_analysis(
                graph,
                &plan,
                self.indexes.inputs.law().exprs()[guard].span,
                bindings,
            )?;
            guard.analysis.known_value == Some(Scalar::Bool(false))
        } else {
            false
        };
        if !universal_false {
            let (allowed, guard) = frames::body_guard(
                graph,
                index,
                span,
                self.state.cutoff.get().min(graph.nodes.len()),
            )?;
            let guard = guard.ok_or("未評価bodyの前に実guardがない")?;
            self.validate_at(graph, graph.get(guard)?, guard.0)?;
            let Some(Payload::Evaluation { value, .. }) = &graph.get(guard)?.payload else {
                return Err("実guardが評価でない".into());
            };
            if allowed || graph.boolean(*value)? != Some(false) {
                return Err("未評価bodyの実guardがfalseでない".into());
            }
        }
        let mut scope = inputs.origin.scope;
        scope.merge(&self.state.architecture_scope());
        Ok(Some(SourceAnalysis {
            condition_failed: false,
            condition_pending: false,
            symbolic: None,
            comparison: None,
            scope,
            known_value: None,
            affine: None,
            missing: None,
            support: vec![],
            scalar_scope: None,
        }))
    }

    pub(super) fn native_law_source_inputs(
        &self,
        graph: &Graph,
        index: usize,
    ) -> Result<Option<FrameInputs>, ValidationFailure> {
        self.tick()?;
        let limit = self.state.cutoff.get().min(graph.nodes.len());
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
        let declaration = self
            .indexes
            .inputs
            .law()
            .declarations()
            .get(&inputs.origin.declaration)
            .ok_or("元Lawの宣言がない")?;
        if let archsig_input::law::model::Signature::Law { params, .. } = &declaration.signature {
            for parameter in params {
                if !variables.contains_key(&parameter.name)
                    && numeric_parameters::numeric_width(&parameter.ty).is_some()
                {
                    let (free, _) = numeric_parameters::law_variables(
                        self,
                        std::slice::from_ref(parameter),
                        &[],
                    )?;
                    variables.extend(free);
                }
            }
        }
        Ok(Some((inputs.bindings, variables, inputs.origin.scope)))
    }
}
