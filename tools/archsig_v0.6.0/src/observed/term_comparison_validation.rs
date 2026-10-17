//! 固定された元body・実Context・子評価から、正規形と再代入を毎回検査する。
use super::*;
type TermProof = (super::super::term::affine::Certificate, SourceAnalysis);
impl Environment<'_> {
    fn term_proof_origin(
        &self,
        graph: &Graph,
        args: &[NodeRef],
        limit: usize,
    ) -> Result<TermProof, ValidationFailure> {
        let [own, le, re, l, r, ..] = args else {
            return Err("Term証拠の元実辺数が違う".into());
        };
        let context = self.current_context(graph);
        if !(own.0 < le.0 && le.0 < re.0 && re.0 < limit) || l.0 >= le.0 || r.0 >= re.0 {
            return Err("Term証拠の既出順が違う".into());
        }
        for reference in [own, le, re, l, r] {
            self.tick()?;
            if reference.0 >= limit || graph.context_at(reference.0) != context {
                return Err("Term証拠が別Contextまたは未出を指す".into());
            }
            self.validate_at(graph, graph.get(*reference)?, reference.0)?;
        }
        let span = self.expression_span(graph, *own)?;
        let law = self.inputs.law();
        let id = *self.expressions.get(&span).ok_or("Term証拠の元ASTがない")?;
        let ExprKind::Binary {
            op: BinOp::Eq | BinOp::Ne,
            lhs,
            rhs,
        } = law.exprs[id].kind
        else {
            return Err("Term証拠の元演算が違う".into());
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
                return Err("Term証拠の元子Source・束縛・値が違う".into());
            }
        }
        let (Scalar::Term(a), Scalar::Term(b)) = (graph.scalar(*l)?, graph.scalar(*r)?) else {
            return Err("Term証拠の左右がTermでない".into());
        };
        let mut infinite = false;
        for (_, t) in &a.params {
            if !super::super::finite::completion_supported(t, law, &self.control)? {
                infinite = true;
            }
        }
        if !infinite {
            return Err("有限Termを無限域の正規形証拠にした".into());
        }
        let expected = super::super::term::affine::comparison(a, b, law, &self.control)?
            .ok_or("元Termの正規形・相違点が作れない")?;
        let analysis = self.resolve_analysis(
            graph,
            self.analyze_source(graph, span, bindings)?,
            &[*le, *re],
        )?;
        Ok((expected, analysis))
    }
    fn term_proof_flags(
        &self,
        node: &Node,
        analysis: &SourceAnalysis,
    ) -> Result<(), ValidationFailure> {
        if node.support != analysis.support
            || node.scope != analysis.scope
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
            || node.judgment.is_some()
        {
            return Err("Term証拠の元支持・Scope・flagsが違う".into());
        }
        Ok(())
    }
    /// 既存のevaluation/binding構成を使う証拠内Scalar。元比較の5辺を必ず保持する。
    pub(super) fn validate_term_presentation_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if !matches!(node.rule, Rule::Construction("evaluation" | "binding")) {
            return Ok(false);
        }
        let [_, le, re, _, _, ..] = node.arguments.as_slice() else {
            return Ok(false);
        };
        if !matches!(graph.get(*le)?.ty, NodeType::Evaluation(Type::Term(..)))
            || !matches!(graph.get(*re)?.ty, NodeType::Evaluation(Type::Term(..)))
        {
            return Ok(false);
        }
        let (certificate, analysis) = self.term_proof_origin(graph, &node.arguments, limit)?;
        self.term_proof_flags(node, &analysis)?;
        let [_, _, _, l, r, rest @ ..] = node.arguments.as_slice() else {
            unreachable!()
        };
        let actual = match &node.payload {
            Some(Payload::Scalar(v)) => v,
            _ => return Err("Term証拠内値がScalarでない".into()),
        };
        if matches!(node.rule, Rule::Construction("binding")) {
            let point = certificate
                .point
                .as_ref()
                .ok_or("相違点がないTermの引数値")?;
            if !rest.is_empty() || !point.arguments.contains(actual) {
                return Err("Term相違点の元引数値が違う".into());
            }
        } else {
            let [selected, arguments @ ..] = rest else {
                return Err("Term正規形/再代入の選択元がない".into());
            };
            if ![*l, *r].contains(selected) {
                return Err("Term正規形/再代入が別の元Termを使う".into());
            }
            let Scalar::Term(term) = graph.scalar(*selected)? else {
                return Err("元Termがない".into());
            };
            let expected = if arguments.is_empty() {
                certificate.presentation(term, *selected == *l, &self.control)?
            } else {
                let point = certificate
                    .point
                    .as_ref()
                    .ok_or("元Term比較に再代入点がない")?;
                if arguments.len() != point.arguments.len() {
                    return Err("元Term再代入の引数数が違う".into());
                }
                let mut values = vec![];
                for (reference, wanted) in arguments.iter().zip(&point.arguments) {
                    self.validate_term_point_argument(
                        graph,
                        *reference,
                        &node.arguments[..5],
                        wanted,
                        limit,
                    )?;
                    values.push(graph.scalar(*reference)?.clone());
                }
                let value = term.apply(&values, self.inputs.law(), &self.control)?;
                let wanted = if *selected == *l {
                    &point.left
                } else {
                    &point.right
                };
                if &value != wanted {
                    return Err("元Termの相違点再代入が係数からの点と違う".into());
                }
                value
            };
            if actual != &expected {
                return Err("Termの正規形または元body再代入値が違う".into());
            }
        }
        if node.ty != NodeType::Value(actual.ty()) {
            return Err("Term証拠内Scalarの型が違う".into());
        }
        Ok(true)
    }
    fn validate_term_point_argument(
        &self,
        graph: &Graph,
        reference: NodeRef,
        base: &[NodeRef],
        wanted: &Scalar,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        if reference.0 >= limit || graph.context_at(reference.0) != self.current_context(graph) {
            return Err("Term相違点引数が別Contextまたは未出".into());
        }
        let node = graph.get(reference)?;
        if node.arguments != base
            || !matches!(node.rule, Rule::Construction("binding"))
            || graph.scalar(reference)? != wanted
        {
            return Err("Term相違点引数の元比較・型付き値が違う".into());
        }
        self.validate_at(graph, node, reference.0)
    }
    pub(super) fn validate_term_comparison_evidence(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let (expected, analysis) = self.term_proof_origin(graph, &node.arguments, limit)?;
        self.term_proof_flags(node, &analysis)?;
        if node.ty != NodeType::Evidence || !matches!(node.rule, Rule::Construction("evidence")) {
            return Err("Term比較証拠の型・規則が違う".into());
        }
        let [source, _, _, l, r, rest @ ..] = node.arguments.as_slice() else {
            unreachable!()
        };
        match &node.payload {
            Some(Payload::TermComparison {
                source: own,
                left,
                right,
                certificate,
                before,
                after,
            }) => {
                if rest != [*before, *after]
                    || own != source
                    || left != l
                    || right != r
                    || !([*l, *r].contains(before))
                    || !certificate.identical(&expected, &self.control)?
                {
                    return Err("Term正規化の元左右・係数証明が違う".into());
                }
                if after.0 >= limit || graph.context_at(after.0) != self.current_context(graph) {
                    return Err("Term正規形が別Contextまたは未出".into());
                }
                let normal = graph.get(*after)?;
                let mut args = node.arguments[..5].to_vec();
                args.push(*before);
                if normal.arguments != args
                    || !matches!(normal.rule, Rule::Construction("evaluation"))
                {
                    return Err("Term正規形が別の元producerを使う".into());
                }
                self.validate_at(graph, normal, after.0)?;
            }
            Some(Payload::TermCounterexample {
                bindings,
                left,
                right,
                facts,
            }) => {
                let point = expected.point.as_ref().ok_or("元比較に相違点がない")?;
                let Scalar::Term(term) = graph.scalar(*l)? else {
                    unreachable!()
                };
                if bindings.len() != term.params.len() || facts != &analysis.support {
                    return Err("Term反例の元parameter・支持が違う".into());
                }
                let mut args = node.arguments[..5].to_vec();
                for (((name, ty), wanted), binding) in
                    term.params.iter().zip(&point.arguments).zip(bindings)
                {
                    if &binding.name != name || &binding.ty != ty || &wanted.ty() != ty {
                        return Err("Term反例の元名前・型が違う".into());
                    }
                    self.validate_term_point_argument(
                        graph,
                        binding.value,
                        &node.arguments[..5],
                        wanted,
                        limit,
                    )?;
                    args.push(binding.value);
                }
                args.extend([*left, *right]);
                if args != node.arguments {
                    return Err("Term反例の元引数・左右辺が違う".into());
                }
                for (output, selected, wanted) in
                    [(*left, *l, &point.left), (*right, *r, &point.right)]
                {
                    if output.0 >= limit
                        || graph.context_at(output.0) != self.current_context(graph)
                    {
                        return Err("Term反例結果が別Contextまたは未出".into());
                    }
                    let child = graph.get(output)?;
                    let mut args = node.arguments[..5].to_vec();
                    args.push(selected);
                    args.extend(bindings.iter().map(|b| b.value));
                    if child.arguments != args || graph.scalar(output)? != wanted {
                        return Err("Term反例結果の元Term・再代入値が違う".into());
                    }
                    self.validate_at(graph, child, output.0)?;
                }
                if point.left == point.right {
                    return Err("Term反例の再代入結果が等しい".into());
                }
            }
            _ => return Err("Term比較証拠でない".into()),
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
            return Err("Term比較値の左右がTermでない".into());
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
                return Err("算法外/有限Term比較に係数証拠がある".into());
            }
            return Ok(());
        };
        if node.evidence.len() != if expected.equal() { 2 } else { 3 } {
            return Err("Term比較値の左右正規形・反例数が違う".into());
        }
        for (index, reference) in node.evidence.iter().enumerate() {
            if reference.0 >= limit || graph.context_at(reference.0) != self.current_context(graph)
            {
                return Err("Term比較値の証拠が別Contextまたは未出".into());
            }
            let evidence = graph.get(*reference)?;
            self.validate_at(graph, evidence, reference.0)?;
            let [source, _, _, left, right, ..] = evidence.arguments.as_slice() else {
                return Err("Term比較証拠の元辺がない".into());
            };
            if left != l
                || right != r
                || self.expression_span(graph, *source)? != *span
                || evidence.support != node.support
                || evidence.scope != node.scope
            {
                return Err("Term比較値の元Source・左右・支持・Scopeが違う".into());
            }
            match (index, &evidence.payload) {
                (
                    0 | 1,
                    Some(Payload::TermComparison {
                        before,
                        certificate,
                        ..
                    }),
                ) if *before == if index == 0 { *l } else { *r }
                    && certificate.identical(&expected, &self.control)? => {}
                (2, Some(Payload::TermCounterexample { .. })) => {}
                _ => return Err("Term比較値の証拠の対応・順が違う".into()),
            }
        }
        let value = if op == BinOp::Eq {
            expected.equal()
        } else {
            !expected.equal()
        };
        if node.payload != Some(Payload::Scalar(Scalar::Bool(value))) {
            return Err("Term比較値の元判断が違う".into());
        }
        Ok(())
    }
}
