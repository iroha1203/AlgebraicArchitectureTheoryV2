//! 元TypeAstのowner添字は式ではない。実束縛が完成した量化の評価時にだけSourceを作る。
use super::*;

impl Evaluator<'_, '_> {
    pub(super) fn prepare_source_child(&mut self, id: ExprId) -> Result<(), Failure> {
        if let ExprKind::Quant {
            split:
                crate::law::ast::QuantSplit::Fixed {
                    domain: crate::law::ast::QuantDomain::Type(original),
                    ..
                },
            ..
        } = &self.environment.inputs.law().exprs[id].kind
            && super::super::quantifier::has_owner(original, self.control)?
        {
            self.tick(Checkpoint::FiniteIteration)?;
            return Ok(());
        }
        self.prepare_source(id)?;
        Ok(())
    }

    pub(super) fn owned_type_reasons(
        &mut self,
        source: NodeRef,
        element: &Type,
        type_span: (usize, usize),
        missing: Vec<Fact>,
    ) -> Vec<Reason> {
        let mut reasons = Vec::new();
        if !missing.is_empty() {
            reasons.push(Reason {
                kind: ReasonKind::Missing,
                request: self.request.id.clone(),
                dependencies: vec![source],
                missing,
                location: Some(Location::Law { span: type_span }),
            });
        }
        reasons.push(Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: self.request.kind,
                operand_types: vec![element.clone()],
                method: "unresolved_owned_type_quantification".into(),
            },
            request: self.request.id.clone(),
            dependencies: vec![source],
            missing: vec![],
            location: Some(Location::Law { span: type_span }),
        });
        self.reasons.extend(reasons.iter().cloned());
        reasons
    }
}
