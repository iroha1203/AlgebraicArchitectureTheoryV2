//! 元Termの正規形と相違点を、標準EvidenceDataの既出参照で保持する。
use super::*;
impl Evaluator<'_, '_> {
    fn term_proof_node(
        &mut self,
        payload: Payload,
        rule: &'static str,
        arguments: Vec<NodeRef>,
        support: &[Fact],
        scope: &Scope,
    ) -> Result<NodeRef, Failure> {
        let ty = match &payload {
            Payload::Scalar(v) => NodeType::Value(v.ty()),
            _ => NodeType::Evidence,
        };
        self.push(Node {
            ty,
            payload: Some(payload),
            rule: Rule::Construction(rule),
            arguments,
            support: support.to_vec(),
            scope: scope.clone(),
            evidence: vec![],
            judgment: None,
            reasons: vec![],
        })
    }
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
        let (a, b) = (a.clone(), b.clone());
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
        let Some(certificate) = super::super::term::affine::comparison(&a, &b, law, self.control)?
        else {
            return Ok(vec![]);
        };
        let source = self
            .sources
            .get(&span)
            .ok_or_else(|| Failure::Internal("Term比較の元Sourceがない".into()))?
            .expression;
        let base = vec![source, left.evaluation, right.evaluation, l, r];
        let mut evidence = vec![];
        for (before, is_left, term) in [(l, true, &a), (r, false, &b)] {
            let normal = certificate.presentation(term, is_left, self.control)?;
            let mut args = base.clone();
            args.push(before);
            let after =
                self.term_proof_node(Payload::Scalar(normal), "evaluation", args, support, scope)?;
            let mut args = base.clone();
            args.extend([before, after]);
            evidence.push(self.term_proof_node(
                Payload::TermComparison {
                    source,
                    left: l,
                    right: r,
                    certificate: Box::new(certificate.clone()),
                    before,
                    after,
                },
                "evidence",
                args,
                support,
                scope,
            )?);
        }
        if let Some(point) = &certificate.point {
            let mut bindings = vec![];
            for ((name, ty), value) in a.params.iter().zip(&point.arguments) {
                let reference = self.term_proof_node(
                    Payload::Scalar(value.clone()),
                    "binding",
                    base.clone(),
                    support,
                    scope,
                )?;
                bindings.push(Binding {
                    name: name.clone(),
                    ty: ty.clone(),
                    value: reference,
                });
            }
            let mut outputs = vec![];
            for (selected, value) in [(l, &point.left), (r, &point.right)] {
                let mut args = base.clone();
                args.push(selected);
                args.extend(bindings.iter().map(|b| b.value));
                outputs.push(self.term_proof_node(
                    Payload::Scalar(value.clone()),
                    "evaluation",
                    args,
                    support,
                    scope,
                )?);
            }
            let mut args = base;
            args.extend(bindings.iter().map(|b| b.value));
            args.extend(&outputs);
            evidence.push(self.term_proof_node(
                Payload::TermCounterexample {
                    bindings,
                    left: outputs[0],
                    right: outputs[1],
                    facts: support.to_vec(),
                },
                "evidence",
                args,
                support,
                scope,
            )?);
        }
        Ok(evidence)
    }
}
