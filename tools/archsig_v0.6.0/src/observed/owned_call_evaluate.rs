//! callerへ戻した後、元callの所属条件と通常値を別々に構成する。
use super::*;

impl Evaluator<'_, '_> {
    pub(super) fn owned_call_finish(
        &mut self,
        span: (usize, usize),
        ty: Type,
        children: Vec<Evaluated>,
        known: Option<Scalar>,
        checks: super::super::environment::owned_call::Checks,
    ) -> Result<Evaluated, Failure> {
        let source = self
            .sources
            .get(&span)
            .ok_or_else(|| Failure::Internal("Owned callの元Sourceがない".into()))?
            .clone();
        self.owned_call_finish_at(source, span, ty, children, known, checks)
    }

    pub(super) fn owned_call_finish_at(
        &mut self,
        source: SourceHandle,
        span: (usize, usize),
        ty: Type,
        children: Vec<Evaluated>,
        known: Option<Scalar>,
        checks: super::super::environment::owned_call::Checks,
    ) -> Result<Evaluated, Failure> {
        let mut scope = source.scope.clone();
        scope.merge(&checks.scope);
        let mut support = checks.support.clone();
        let edges: Vec<_> = std::iter::once(source.expression)
            .chain(children.iter().map(|c| c.evaluation))
            .collect();
        for child in &children {
            self.tick(Checkpoint::FiniteIteration)?;
            scope.merge(&child.scope);
            support.extend(child.support.iter().cloned());
        }
        support.sort();
        support.dedup();
        let mut reasons = Vec::new();
        let value = if let Some((actual, required)) = checks.failure {
            #[cfg(test)]
            data::observe_actual(span, self.graph.active, "owned_call_condition", 0);
            self.tick(Checkpoint::FiniteIteration)?;
            let left = self.value(
                actual,
                Rule::Construction("evaluation"),
                edges.clone(),
                support.clone(),
                scope.clone(),
            )?;
            let right = self.value(
                required,
                Rule::Construction("domain"),
                edges.clone(),
                support.clone(),
                scope.clone(),
            )?;
            let evidence = self.push(Node {
                ty: NodeType::Evidence,
                payload: Some(Payload::OwnedCallCounterexample {
                    bindings: self.bindings.clone(),
                    left,
                    right,
                    facts: support.clone(),
                }),
                rule: Rule::Construction("evidence"),
                arguments: edges.iter().copied().chain([left, right]).collect(),
                support: support.clone(),
                scope: scope.clone(),
                evidence: vec![],
                judgment: None,
                reasons: vec![],
            })?;
            let condition = self.push(Node {
                ty: NodeType::Proposition,
                payload: Some(Payload::OwnedCallCondition { left, right }),
                rule: Rule::Construction("proposition"),
                arguments: edges
                    .iter()
                    .copied()
                    .chain([left, right, evidence])
                    .collect(),
                support: support.clone(),
                scope: scope.clone(),
                evidence: vec![evidence],
                judgment: Some(Judgment {
                    status: Decision::Refuted,
                    evidence: vec![evidence],
                    reasons: vec![],
                }),
                reasons: vec![],
            })?;
            reasons.push(Reason {
                kind: ReasonKind::ConditionFailed {
                    condition,
                    construction: "evaluation",
                },
                request: self.request.id.clone(),
                dependencies: vec![source.expression],
                missing: vec![],
                location: Some(Location::Law { span }),
            });
            None
        } else if checks.blocked {
            None
        } else if let Some(value) = known {
            Some(self.value(
                value,
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                },
                children.iter().map(|c| c.evaluation).collect(),
                support,
                scope,
            )?)
        } else {
            None
        };
        let previous = self.sources.insert(span, source);
        let result = self.finish_with_reasons(
            span,
            ty,
            value,
            children,
            checks.support,
            None,
            None,
            None,
            reasons,
        );
        if let Some(previous) = previous {
            self.sources.insert(span, previous);
        } else {
            self.sources.remove(&span);
        }
        result
    }
}
