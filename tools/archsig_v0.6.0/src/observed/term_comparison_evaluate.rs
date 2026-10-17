//! 元のTerm比較に、係数の全有限caseまたは再代入した相違点を保持する。
use super::*;
impl Evaluator<'_, '_> {
    pub(super) fn term_comparison_evidence(
        &mut self,
        span: (usize, usize),
        op: BinOp,
        left: &Evaluated,
        right: &Evaluated,
        support: &[Fact],
        scope: &Scope,
    ) -> Result<Vec<NodeRef>, Failure> {
        if !matches!(op, BinOp::Eq | BinOp::Ne) {
            return Ok(vec![]);
        }
        let Some((l, r)) = left.value.zip(right.value) else {
            return Ok(vec![]);
        };
        let (Scalar::Term(a), Scalar::Term(b)) = (self.graph.scalar(l)?, self.graph.scalar(r)?)
        else {
            return Ok(vec![]);
        };
        let law = self.environment.inputs.law();
        let mut infinite = false;
        for (_, t) in &a.params {
            if !super::super::finite::completion_supported(t, law, self.control)? {
                infinite = true;
            }
        }
        if !infinite {
            return Ok(vec![]);
        }
        let Some(certificate) = super::super::term::affine::comparison(a, b, law, self.control)?
        else {
            return Ok(vec![]);
        };
        let source = self
            .sources
            .get(&span)
            .ok_or_else(|| Failure::Internal("Term比較の元Sourceがない".into()))?
            .expression;
        let evidence = self.push(Node {
            ty: NodeType::Evidence,
            payload: Some(Payload::TermComparison {
                source,
                left: l,
                right: r,
                certificate: Box::new(certificate),
            }),
            rule: Rule::Construction("evidence"),
            arguments: vec![source, left.evaluation, right.evaluation, l, r],
            support: support.to_vec(),
            scope: scope.clone(),
            evidence: vec![],
            judgment: None,
            reasons: vec![],
        })?;
        Ok(vec![evidence])
    }
}
