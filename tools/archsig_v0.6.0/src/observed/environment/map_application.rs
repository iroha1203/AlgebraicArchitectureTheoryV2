//! Map適用の定義条件を、元Source・実子評価と不変の入力から再検査する。
use super::*;

pub(in crate::observed) struct MapCondition {
    pub actual: Scalar,
    pub required: Scalar,
    pub scope: Scope,
    pub support: Vec<Fact>,
    pub bindings: Vec<Binding>,
}
impl Environment<'_> {
    fn map_call(
        &self,
        graph: &Graph,
        source: NodeRef,
    ) -> Result<Option<[usize; 2]>, ValidationFailure> {
        if !matches!(
            graph.get(source)?.payload,
            Some(Payload::Expression {
                location: Location::Law { .. },
                ..
            })
        ) {
            return Ok(None);
        }
        let span = self.expression_span(graph, source)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(None);
        };
        let law = self.inputs.law();
        let ExprKind::Call { callee, args } = &law.exprs[id].kind else {
            return Ok(None);
        };
        if !matches!(law.expr_type(*callee), Some(Type::Map(..))) {
            return Ok(None);
        }
        if args.len() != 1 {
            return Err("Map元適用のarityが違う".into());
        }
        Ok(Some([*callee, args[0]]))
    }
    pub(in crate::observed) fn map_condition(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<Option<MapCondition>, ValidationFailure> {
        self.tick()?;
        let Some(ids) = self.map_call(graph, source)? else {
            return Ok(None);
        };
        let [map, key] = children else {
            return Err("Map条件の実子数が違う".into());
        };
        let Some(Payload::Expression { bindings, .. }) = &graph.get(source)?.payload else {
            return Err("Map条件の元Sourceがない".into());
        };
        let context = self.current_context(graph);
        for r in [source, *map, *key] {
            self.tick()?;
            if r.0 >= limit || graph.context_at(r.0) != context {
                return Err("Map条件のproducerが既出同Contextでない".into());
            }
            self.validate_at(graph, graph.get(r)?, r.0)?;
        }
        let mut values = Vec::new();
        let mut scope = graph.get(source)?.scope.clone();
        let mut support = Vec::new();
        for (r, id) in children.iter().zip(ids) {
            self.tick()?;
            let (expression, actual_bindings, value) = self.evaluation(graph, *r)?;
            self.source_matches(graph, expression, id)?;
            if actual_bindings != bindings {
                return Err("Map条件の元束縛と実子が違う".into());
            }
            let Some(value) = value else {
                return Ok(None);
            };
            self.validate_at(graph, graph.get(value)?, value.0)?;
            values.push(graph.scalar(value)?.clone());
            scope.merge(&graph.get(*r)?.scope);
            support.extend(graph.get(*r)?.support.iter().cloned());
        }
        let Scalar::Map { domain, pairs, .. } = &values[0] else {
            return Err("Map条件の実calleeがMap値でない".into());
        };
        if data::map_apply(&values[0], &values[1], self.inputs.law(), &self.control)?.is_some() {
            return Ok(None);
        }
        let mut keys = Vec::new();
        for (key, _) in pairs {
            self.tick()?;
            keys.push(key.clone());
        }
        let required = data::set(domain.clone(), &keys, &self.control)?;
        keys.push(values[1].clone());
        let actual = data::set(domain.clone(), &keys, &self.control)?;
        if data::equal(&actual, &required, &self.control)? {
            return Err("域外Map条件の反証が成立しない".into());
        }
        support.sort();
        support.dedup();
        self.tick()?;
        Ok(Some(MapCondition {
            actual,
            required,
            scope,
            support,
            bindings: bindings.clone(),
        }))
    }
    fn map_condition_proof_inputs(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<Option<MapCondition>, ValidationFailure> {
        let Some(source) = node.arguments.first().copied() else {
            return Ok(None);
        };
        if !matches!(graph.get(source)?.ty, NodeType::Expression(_))
            || self.map_call(graph, source)?.is_none()
        {
            return Ok(None);
        }
        if node.arguments.len() < 3 {
            return Err("Map条件の実子辺がない".into());
        }
        self.map_condition(graph, source, &node.arguments[1..3], limit)
    }
    pub(super) fn validate_map_condition_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let candidate = matches!(&node.payload, Some(Payload::MapDomainCondition { .. }))
            || matches!(
                (&node.payload, &node.rule),
                (
                    Some(Payload::Scalar(Scalar::Set { .. })),
                    Rule::Construction("evaluation" | "domain")
                )
            )
            || matches!(
                (&node.payload, &node.rule),
                (
                    Some(Payload::Counterexample { .. }),
                    Rule::Construction("evidence")
                )
            );
        if !candidate {
            return Ok(false);
        }
        let Some(expected) = self.map_condition_proof_inputs(graph, node, limit)? else {
            if matches!(node.payload, Some(Payload::MapDomainCondition { .. })) {
                return Err("Map条件命題に元域外適用がない".into());
            }
            return Ok(false);
        };
        if node.support != expected.support
            || node.scope != expected.scope
            || !node.reasons.is_empty()
        {
            return Err("Map条件の元支持・Scope・理由が違う".into());
        }
        for r in &node.arguments {
            self.tick()?;
            if graph.context_at(r.0) != self.current_context(graph) {
                return Err("Map条件が別producerを転用した".into());
            }
        }
        match &node.payload {
            Some(Payload::Scalar(value)) => {
                let expected_value = match node.rule {
                    Rule::Construction("evaluation") => &expected.actual,
                    Rule::Construction("domain") => &expected.required,
                    _ => return Err("Map条件集合の役割が違う".into()),
                };
                if node.arguments.len() != 3
                    || node.ty != NodeType::Value(value.ty())
                    || !node.evidence.is_empty()
                    || node.judgment.is_some()
                    || value.ty() != expected.actual.ty()
                    || !data::equal(value, expected_value, &self.control)?
                {
                    return Err("Map条件集合値が元key全域・実引数と違う".into());
                }
            }
            Some(Payload::Counterexample {
                bindings,
                left,
                right,
                facts,
            }) => {
                if !graph.map_domain_counterexample_shape(node)?
                    || bindings != &expected.bindings
                    || facts != &expected.support
                    || node.arguments.get(3) != Some(left)
                    || node.arguments.get(4) != Some(right)
                {
                    return Err("Map条件反例の元値・束縛・支持が違う".into());
                }
                for r in [*left, *right] {
                    self.validate_at(graph, graph.get(r)?, r.0)?;
                }
                if !data::equal(graph.scalar(*left)?, &expected.actual, &self.control)?
                    || !data::equal(graph.scalar(*right)?, &expected.required, &self.control)?
                {
                    return Err("Map条件反例が元key集合等値の不成立でない".into());
                }
            }
            Some(Payload::MapDomainCondition { left, right }) => {
                if node.ty != NodeType::Proposition {
                    return Err("Map条件命題のnode型が違う".into());
                }
                graph.validate_proposition_evidence(node)?;
                if node.arguments.len() != 6 {
                    return Err("Map条件命題の辺数が違う".into());
                }
                for r in [*left, *right, node.arguments[5]] {
                    self.validate_at(graph, graph.get(r)?, r.0)?;
                }
                if !data::equal(graph.scalar(*left)?, &expected.actual, &self.control)?
                    || !data::equal(graph.scalar(*right)?, &expected.required, &self.control)?
                {
                    return Err("Map条件命題が元実keyを判定していない".into());
                }
            }
            _ => return Err("Map条件のpayloadが違う".into()),
        }
        self.tick()?;
        Ok(true)
    }
    pub(super) fn map_condition_reason(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<Option<Reason>, ValidationFailure> {
        if self
            .map_condition(graph, source, children, limit)?
            .is_none()
        {
            return Ok(None);
        }
        let mut found = None;
        for (index, node) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if graph.context_at(index) == self.current_context(graph)
                && matches!(node.payload, Some(Payload::MapDomainCondition { .. }))
                && node.arguments.get(..3) == Some([source, children[0], children[1]].as_slice())
            {
                self.validate_at(graph, node, index)?;
                if found.replace(NodeRef(index)).is_some() {
                    return Err("元Map適用の条件命題が重複した".into());
                }
            }
        }
        let condition = found.ok_or("域外Map適用の条件命題がない")?;
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("Map条件の元Requestがない")?;
        Ok(Some(Reason {
            kind: ReasonKind::ConditionFailed {
                condition,
                construction: "evaluation",
            },
            request: request.id.clone(),
            dependencies: vec![source],
            missing: vec![],
            location: Some(Location::Law {
                span: self.expression_span(graph, source)?,
            }),
        }))
    }
}
