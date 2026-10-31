//! 実際の有限量化の全caseから、外側全称の真偽を読む。
use super::*;
impl Environment<'_> {
    pub(super) fn universal_completed_pointwise(
        &self,
        graph: &Graph,
        template: NodeRef,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<Option<NodeRef>, ValidationFailure> {
        let mut found = None;
        let context = self.current_context(graph);
        for (index, node) in graph.nodes.iter().enumerate().take(self.cutoff.get()) {
            self.tick()?;
            if graph.context_at(index) != context {
                continue;
            }
            let Some(Payload::Evaluation {
                expression,
                bindings: actual,
                ..
            }) = &node.payload
            else {
                continue;
            };
            if actual != bindings || *expression == template {
                continue;
            }
            let source = graph.get(*expression)?;
            if source.arguments.first() != Some(&template)
                || !matches!(&source.payload, Some(Payload::Expression { location: Location::Law { span: actual }, .. }) if *actual == span)
            {
                continue;
            }
            if found.replace(NodeRef(index)).is_some() {
                return Err("全域pointwiseの元出現・Contextが一意でない".into());
            }
        }
        Ok(found)
    }
    pub(super) fn universal_finite_decision(
        &self,
        graph: &Graph,
        template: NodeRef,
        plan: &UniversalPlan,
        bindings: &[Binding],
    ) -> Result<Option<(bool, NodeRef)>, ValidationFailure> {
        if !self.universal_finite_syntax(plan.body)?
            || !matches!(
                self.inputs.law().exprs[plan.body].kind,
                ExprKind::Quant { .. }
            )
        {
            return Ok(None);
        }
        let Some(evaluation) = self.universal_completed_pointwise(
            graph,
            template,
            self.inputs.law().exprs[plan.body].span,
            bindings,
        )?
        else {
            return Ok(None);
        };
        self.recheck_evaluation(graph, evaluation)?;
        let node = graph.get(evaluation)?;
        let Some(Payload::Evaluation {
            expression, parts, ..
        }) = &node.payload
        else {
            unreachable!()
        };
        let spec = quantifier::spec(self.inputs.law(), plan.body, &self.control)?;
        let has_domain = node.scope.quantifiers.iter().any(|q| {
            q.occurrence == spec.span
                && q.context == Some(self.current_context(graph))
                && q.domain.is_some_and(|domain| {
                    matches!(
                        graph.get(domain).map(|n| &n.payload),
                        Ok(Some(Payload::Domain { .. }))
                    )
                })
        });
        if !has_domain {
            return Ok(None);
        }
        let [part] = parts.as_slice() else {
            return Err("全域有限量化の元partが一つでない".into());
        };
        let cases = part
            .children
            .get(usize::from(spec.domain.is_some())..)
            .ok_or("全域有限量化のcollection辺がない")?;
        let mut decisions = Vec::new();
        for &body in cases {
            self.tick()?;
            let (source, actual, _) = self.evaluation(graph, body)?;
            let analysis = self.original_evaluation_source(graph, body, source, actual)?;
            if analysis.condition_failed || analysis.condition_pending {
                return Ok(None);
            }
            let constant = match analysis.known_value {
                Some(Scalar::Bool(value)) => Some(value),
                _ => None,
            };
            let decision = if constant.is_some() {
                constant
            } else if let Some(predicate) =
                analysis.comparison.as_ref().filter(|p| p.op == BinOp::Eq)
            {
                affine::universal_equality(
                    Some(&predicate.left),
                    Some(&predicate.right),
                    &self.universal_closed_parameters(plan, predicate)?,
                    &self.control,
                )?
                .and_then(|result| result.value)
            } else {
                None
            };
            // 異なる数値反例を持つ有限existsの各caseから、共通の反例は導けない。
            decisions.push(
                if spec.kind == QuantKind::Exists
                    && cases.len() != 1
                    && constant != Some(false)
                    && decision != Some(true)
                {
                    None
                } else {
                    decision
                },
            );
        }
        Ok(quantifier::reduce(spec.kind, &decisions, &self.control)?
            .map(|value| (value, *expression)))
    }
}
