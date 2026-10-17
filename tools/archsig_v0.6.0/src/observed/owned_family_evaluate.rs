//! 元Family式と実owner子Evaluationを、原所属から読んだSetへ接続する。
use super::*;

impl Evaluator<'_, '_> {
    pub(super) fn owned_family(
        &mut self,
        id: usize,
        owner_id: usize,
        span: (usize, usize),
        ty: Type,
    ) -> Result<Evaluated, Failure> {
        let owner = self.eval(owner_id)?;
        #[cfg(test)]
        data::observe_actual(span, self.graph.active, "owned_family_begin", 0);
        self.tick(Checkpoint::FiniteIteration)?;
        let known = owner
            .value
            .map(|value| self.graph.scalar(value))
            .transpose()?;
        #[cfg(test)]
        let context = self.graph.active;
        let members =
            self.environment
                .owned_expression_members(id, known, &mut |_phase, _index| {
                    #[cfg(test)]
                    data::observe_actual(span, context, "owned_family_enum", _index);
                })?;
        let source = self
            .sources
            .get(&span)
            .ok_or_else(|| Failure::Internal("所属式族の元Sourceがない".into()))?
            .clone();
        let mut scope = source.scope;
        scope.merge(&owner.scope);
        scope.merge(&members.enumeration.scope);
        let own_support = members.enumeration.support;
        let mut support = own_support.clone();
        support.extend(owner.support.iter().cloned());
        support.sort();
        support.dedup();
        let unresolved = known.is_none() || !members.missing.is_empty();
        let mut reasons = Vec::new();
        if !members.missing.is_empty() {
            reasons.push(Reason {
                kind: ReasonKind::Missing,
                request: self.request.id.clone(),
                dependencies: vec![source.expression],
                missing: members.missing,
                location: Some(Location::Law { span }),
            });
        }
        if unresolved {
            reasons.push(Reason {
                kind: ReasonKind::UnsupportedAlgorithm {
                    question: self.request.kind,
                    operand_types: vec![ty.clone()],
                    method: "unresolved_owned_expression_family".into(),
                },
                request: self.request.id.clone(),
                dependencies: vec![source.expression],
                missing: vec![],
                location: Some(Location::Law { span }),
            });
        }
        self.reasons.extend(reasons.iter().cloned());
        self.retained_scope.merge(&scope);
        let value = if unresolved {
            None
        } else {
            let Type::Set(element) = &ty else {
                return Err(Failure::Internal("所属式族の結果型がSetでない".into()));
            };
            Some(self.value(
                data::set(
                    (**element).clone(),
                    &members.enumeration.values,
                    self.control,
                )?,
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                },
                vec![source.expression, owner.evaluation],
                support,
                scope,
            )?)
        };
        if value.is_some() {
            #[cfg(test)]
            data::observe_actual(span, self.graph.active, "owned_family_set", 0);
            self.tick(Checkpoint::FiniteIteration)?;
        }
        self.finish_with_reasons(
            span,
            ty,
            value,
            vec![owner],
            own_support,
            None,
            None,
            None,
            reasons,
        )
    }
}
