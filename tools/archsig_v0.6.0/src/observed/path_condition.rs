//! 内部Pathの参照構造不一致を元入力から再検査する。
use super::*;
struct Condition {
    left: Scalar,
    right: Scalar,
    bindings: Vec<Binding>,
    support: Vec<Fact>,
    scope: Scope,
}
impl Environment<'_> {
    fn path_condition(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<Option<Condition>, ValidationFailure> {
        let span = self.expression_span(graph, source)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(None);
        };
        if !self.is_path(id)? {
            return Ok(None);
        }
        let ExprKind::Call { args, .. } = &self.inputs.law().exprs[id].kind else {
            unreachable!()
        };
        if children.len() != args.len() {
            return Err("Path条件の元実子数が違う".into());
        }
        if source.0 >= limit || graph.context_at(source.0) != self.current_context(graph) {
            return Err("Path条件Sourceの既出性・Contextが違う".into());
        }
        let bindings = self.expression_bindings(graph, source)?;
        self.validate_at(graph, graph.get(source)?, source.0)?;
        let mut values = Vec::new();
        let mut support = Vec::new();
        let mut scope = graph.get(source)?.scope.clone();
        for (&arg, &child) in args.iter().zip(children) {
            self.tick()?;
            if child.0 >= limit
                || graph.context_at(child.0) != self.current_context(graph)
                || child != self.actual_evaluation(graph, arg, bindings)?
            {
                return Err("Path条件の実子が元引数でない".into());
            }
            self.validate_at(graph, graph.get(child)?, child.0)?;
            let Some(value) = self.evaluation(graph, child)?.2 else {
                return Ok(None);
            };
            values.push(graph.scalar(value)?.clone());
            support.extend(graph.get(child)?.support.iter().cloned());
            scope.merge(&graph.get(child)?.scope);
        }
        let info = self.internal_path_at(graph, id, &values)?;
        let Some((left, right)) = info.failure else {
            return Ok(None);
        };
        support.extend(info.support);
        support.sort();
        support.dedup();
        scope.merge(&info.scope);
        Ok(Some(Condition {
            left,
            right,
            bindings: bindings.to_vec(),
            support,
            scope,
        }))
    }
    pub(super) fn validate_path_condition_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let path_payload = matches!(
            &node.payload,
            Some(Payload::PathCondition { .. } | Payload::PathCounterexample { .. })
        );
        let candidate = path_payload
            || matches!(
                (&node.payload, &node.rule),
                (Some(Payload::Scalar(_)), Rule::Construction("evaluation"))
            );
        if !candidate {
            return Ok(false);
        }
        let Some(source) = node.arguments.first().copied() else {
            return if path_payload {
                Err("Path条件のSource辺がない".into())
            } else {
                Ok(false)
            };
        };
        let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &graph.get(source)?.payload
        else {
            return if path_payload {
                Err("Path条件の元SourceがLaw式でない".into())
            } else {
                Ok(false)
            };
        };
        let Some(&id) = self.expressions.get(span) else {
            return if path_payload {
                Err("Path条件の元式がない".into())
            } else {
                Ok(false)
            };
        };
        if !self.is_path(id)? {
            return if path_payload {
                Err("Path条件がPath構成から生じていない".into())
            } else {
                Ok(false)
            };
        }
        let ExprKind::Call { args, .. } = &self.inputs.law().exprs[id].kind else {
            unreachable!()
        };
        let children = node
            .arguments
            .get(1..args.len() + 1)
            .ok_or("Path条件の元実子辺がない")?;
        let Some(plan) = self.path_condition(graph, source, children, limit)? else {
            return if path_payload {
                Err("Path条件が元入力から生成されない".into())
            } else {
                Ok(false)
            };
        };
        if node.support != plan.support || node.scope != plan.scope || !node.reasons.is_empty() {
            return Err("Path条件の元支持・Scope・理由が違う".into());
        }
        let edges: Vec<_> = std::iter::once(source)
            .chain(children.iter().copied())
            .collect();
        match &node.payload {
            Some(Payload::Scalar(value)) => {
                if value != &plan.left && value != &plan.right
                    || node.arguments != edges
                    || node.ty != NodeType::Value(plan.left.ty())
                    || node.rule != Rule::Construction("evaluation")
                    || !node.evidence.is_empty()
                    || node.judgment.is_some()
                {
                    return Err("Path条件の参照構造値が元入力と違う".into());
                }
            }
            Some(Payload::PathCounterexample {
                bindings,
                left,
                right,
                facts,
            }) => {
                if bindings != &plan.bindings
                    || facts != &plan.support
                    || graph.scalar(*left)? != &plan.left
                    || graph.scalar(*right)? != &plan.right
                    || node.arguments
                        != edges
                            .iter()
                            .copied()
                            .chain([*left, *right])
                            .collect::<Vec<_>>()
                    || node.ty != NodeType::Evidence
                    || node.rule != Rule::Construction("evidence")
                    || !node.evidence.is_empty()
                    || node.judgment.is_some()
                {
                    return Err("Path条件反例が元実子・参照構造と違う".into());
                }
                for r in [left, right] {
                    if r.0 >= limit || graph.context_at(r.0) != self.current_context(graph) {
                        return Err("Path条件値が外来・未生成".into());
                    }
                    self.validate_at(graph, graph.get(*r)?, r.0)?;
                    if graph.get(*r)?.arguments != edges {
                        return Err("Path条件値が別の元式に属する".into());
                    }
                }
            }
            Some(Payload::PathCondition { left, right }) => {
                let Some(proof) = node.evidence.first().copied() else {
                    return Err("Path条件に反例がない".into());
                };
                if proof.0 >= limit
                    || node.evidence != [proof]
                    || node.arguments
                        != edges
                            .iter()
                            .copied()
                            .chain([*left, *right, proof])
                            .collect::<Vec<_>>()
                    || node.ty != NodeType::Proposition
                    || node.rule != Rule::Construction("proposition")
                    || node.judgment
                        != Some(Judgment {
                            status: Decision::Refuted,
                            evidence: vec![proof],
                            reasons: vec![],
                        })
                {
                    return Err("Path条件の元辺・反証が違う".into());
                }
                self.validate_at(graph, graph.get(proof)?, proof.0)?;
                if !matches!(&graph.get(proof)?.payload,Some(Payload::PathCounterexample{left:a,right:b,..})if a==left&&b==right)
                {
                    return Err("Path条件の証拠両辺が違う".into());
                }
            }
            _ => return Ok(false),
        }
        self.tick()?;
        Ok(true)
    }
    pub(in crate::observed) fn path_condition_reason(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<Option<Reason>, ValidationFailure> {
        if self
            .path_condition(graph, source, children, limit)?
            .is_none()
        {
            return Ok(None);
        }
        let mut found = None;
        for (i, node) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if graph.context_at(i) == self.current_context(graph)
                && matches!(node.payload, Some(Payload::PathCondition { .. }))
                && node.arguments.get(..children.len() + 1)
                    == Some(
                        std::iter::once(source)
                            .chain(children.iter().copied())
                            .collect::<Vec<_>>()
                            .as_slice(),
                    )
            {
                self.validate_at(graph, node, i)?;
                if found.replace(NodeRef(i)).is_some() {
                    return Err("Path条件が重複した".into());
                }
            }
        }
        let condition = found.ok_or("Pathの参照構造不一致の条件命題がない")?;
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("Path条件Requestがない")?;
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
