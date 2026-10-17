//! Term外延の証拠を、固定された元body・実producerから毎回再構成する。
use super::*;
impl Environment<'_> {
    pub(super) fn validate_term_comparison_evidence(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        let Some(Payload::TermComparison {
            source,
            left,
            right,
            certificate,
        }) = &node.payload
        else {
            return Err("Term比較証拠でない".into());
        };
        let [own, le, re, l, r] = node.arguments.as_slice() else {
            return Err("Term比較証拠の元実辺数が違う".into());
        };
        let context = self.current_context(graph);
        if own != source
            || l != left
            || r != right
            || !(own.0 < le.0 && le.0 < re.0 && re.0 < limit)
            || l.0 >= le.0
            || r.0 >= re.0
        {
            return Err("Term比較証拠の元左右・既出順が違う".into());
        }
        for reference in node.arguments.iter() {
            self.tick()?;
            if graph.context_at(reference.0) != context {
                return Err("Term比較証拠が別Contextを指す".into());
            }
            self.validate_at(graph, graph.get(*reference)?, reference.0)?;
        }
        let span = self.expression_span(graph, *own)?;
        let law = self.inputs.law();
        let id = *self
            .expressions
            .get(&span)
            .ok_or("Term比較証拠の元ASTがない")?;
        let ExprKind::Binary {
            op: BinOp::Eq | BinOp::Ne,
            lhs,
            rhs,
        } = law.exprs[id].kind
        else {
            return Err("Term比較証拠の元演算が違う".into());
        };
        let bindings = self.expression_bindings(graph, *own)?;
        for (evaluation, operand, value) in [(*le, lhs, *l), (*re, rhs, *r)] {
            let (actual, bs, computed) = self.evaluation(graph, evaluation)?;
            self.source_matches(graph, actual, operand)?;
            if actual.0 >= evaluation.0
                || graph.context_at(actual.0) != context
                || bs != bindings
                || computed != Some(value)
            {
                return Err("Term比較証拠の元子Source・束縛・値が違う".into());
            }
        }
        let (Scalar::Term(a), Scalar::Term(b)) = (graph.scalar(*l)?, graph.scalar(*r)?) else {
            return Err("Term比較証拠の左右がTermでない".into());
        };
        let expected = super::super::term::affine::comparison(a, b, law, &self.control)?
            .ok_or("元Term比較の正規形・相違点が作れない")?;
        let analysis = self.resolve_analysis(
            graph,
            self.analyze_source(graph, span, bindings)?,
            &[*le, *re],
        )?;
        if !certificate.identical(&expected, &self.control)?
            || node.ty != NodeType::Evidence
            || !matches!(node.rule, Rule::Construction("evidence"))
            || node.support != analysis.support
            || node.scope != analysis.scope
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
            || node.judgment.is_some()
        {
            return Err("Term比較証拠の元正規形・再代入点・支持・Scopeが違う".into());
        }
        Ok(())
    }
    pub(super) fn validate_term_comparison_value(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let Rule::Input {
            kind: "law",
            location: Location::Law { span },
        } = &node.rule
        else {
            return Ok(());
        };
        let Some(&id) = self.expressions.get(span) else {
            return Ok(());
        };
        let law = self.inputs.law();
        let ExprKind::Binary {
            op: op @ (BinOp::Eq | BinOp::Ne),
            lhs,
            ..
        } = law.exprs[id].kind
        else {
            return Ok(());
        };
        if !matches!(law.expr_type(lhs), Some(Type::Term(..))) {
            return Ok(());
        }
        let [l, r] = node.arguments.as_slice() else {
            return Err("Term比較値の元左右がない".into());
        };
        let (Scalar::Term(a), Scalar::Term(b)) = (graph.scalar(*l)?, graph.scalar(*r)?) else {
            return Err("Term比較値の元値がTermでない".into());
        };
        let mut infinite = false;
        for (_, t) in &a.params {
            if !super::super::finite::completion_supported(t, law, &self.control)? {
                infinite = true;
            }
        }
        let expected = if infinite {
            super::super::term::affine::comparison(a, b, law, &self.control)?
        } else {
            None
        };
        let Some(expected) = expected else {
            if !node.evidence.is_empty() {
                return Err("算法外または有限Term比較に別の係数証拠がある".into());
            }
            return Ok(());
        };
        let [reference] = node.evidence.as_slice() else {
            return Err("Term比較値に元係数証拠が一つでない".into());
        };
        if reference.0 >= limit || graph.context_at(reference.0) != self.current_context(graph) {
            return Err("Term比較値の証拠が別Contextまたは未出".into());
        }
        let evidence = graph.get(*reference)?;
        self.validate_at(graph, evidence, reference.0)?;
        let Some(Payload::TermComparison {
            source,
            left,
            right,
            certificate,
        }) = &evidence.payload
        else {
            return Err("Term比較値の証拠が係数証拠でない".into());
        };
        let value = if op == BinOp::Eq {
            expected.equal()
        } else {
            !expected.equal()
        };
        if *left != *l
            || *right != *r
            || self.expression_span(graph, *source)? != *span
            || !certificate.identical(&expected, &self.control)?
            || node.payload != Some(Payload::Scalar(Scalar::Bool(value)))
            || node.scope != evidence.scope
            || node.support != evidence.support
        {
            return Err("Term比較値の元Source・左右・判断・係数証拠が違う".into());
        }
        Ok(())
    }
}
