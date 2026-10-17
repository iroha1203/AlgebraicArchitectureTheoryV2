//! 全域アフィン導出を、提示された正規形を入力にせず元の三入力から照合する。
use super::*;

/// 元missingの証拠値と、その値を説明する実Source。
type WitnessSources = Vec<(Fact, Scalar, NodeRef)>;
/// 証拠caseの再構成結果。型Domainと元body producerを常に保持する。
type WitnessReconstruction<Values> = (Values, Vec<NodeRef>, UniversalAnalysis, NodeRef);
type SourceExpectation = (UniversalSourceAnalysis, Vec<NodeRef>);

struct EvaluationPayload<'n> {
    expression: NodeRef,
    bindings: &'n [Binding],
    parts: &'n [Part],
    value: Option<NodeRef>,
    applicability: &'n str,
}

/// 元の局所全称binder。外側Planの全称軸とは区別する。
struct LocalQuantifier {
    template: NodeRef,
    plan: UniversalPlan,
    domains: Vec<NodeRef>,
    parameter: affine::Parameter,
}

struct LocalEvaluation {
    arguments: Vec<NodeRef>,
    analysis: SourceAnalysis,
    scope: Scope,
}

struct ParameterScalarProducer {
    source: NodeRef,
    ty: Type,
    value: Scalar,
    binder: (usize, usize),
}

fn evaluation_payload(node: &Node) -> Result<EvaluationPayload<'_>, ValidationFailure> {
    let Some(Payload::Evaluation {
        expression,
        bindings,
        parts,
        value,
        applicability,
    }) = &node.payload
    else {
        return Err("全域評価のpayloadがEvaluationでない".into());
    };
    Ok(EvaluationPayload {
        expression: *expression,
        bindings,
        parts,
        value: *value,
        applicability,
    })
}

fn reasons_equal(left: &[Reason], right: &[Reason]) -> bool {
    left.iter().map(Reason::wire).collect::<Vec<_>>()
        == right.iter().map(Reason::wire).collect::<Vec<_>>()
}

impl Environment<'_> {
    fn universal_witness_reasons(
        &self,
        graph: &Graph,
        template: NodeRef,
        plan: &UniversalPlan,
        body: NodeRef,
        limit: usize,
    ) -> Result<Vec<Reason>, ValidationFailure> {
        let mut reasons = graph.get(body)?.reasons.clone();
        if let Some(guard) = plan.guard {
            let span = self.inputs.law().exprs[guard].span;
            let mut producer = None;
            for (index, node) in graph.nodes.iter().enumerate().take(limit).rev() {
                self.tick()?;
                if let Some(Payload::Evaluation { expression, .. }) = &node.payload
                    && graph.context_at(index) == graph.context_at(template.0)
                    && matches!(&graph.get(*expression)?.payload,Some(Payload::Expression {location:Location::Law {span:actual},..}) if *actual==span)
                    && graph.get(*expression)?.arguments.first() == Some(&template)
                {
                    producer = Some(NodeRef(index));
                    break;
                }
            }
            let producer = producer.ok_or("数値補完対の元guard実評価がない")?;
            self.recheck_evaluation(graph, producer)?;
            if graph.boolean(self.evaluation(graph, producer)?.2)? != Some(true) {
                return Err("数値補完対のguardが成立済みでない".into());
            }
            reasons.extend(graph.get(producer)?.reasons.iter().cloned());
        }
        sort_reasons(&mut reasons);
        Ok(reasons)
    }
    fn universal_body_producer(
        &self,
        graph: &Graph,
        template: NodeRef,
        plan: &UniversalPlan,
        limit: usize,
    ) -> Result<NodeRef, ValidationFailure> {
        for (index, node) in graph.nodes.iter().enumerate().take(limit).rev() {
            self.tick()?;
            if let Some(Payload::Evaluation { expression, .. }) = &node.payload
                && graph.context_at(index) == graph.context_at(template.0)
                && matches!(&graph.get(*expression)?.payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==plan.template_span)
                && graph.get(*expression)?.arguments.first() == Some(&template)
            {
                return Ok(NodeRef(index));
            }
        }
        Err("全域証拠に先行する実body評価がない".into())
    }

    fn universal_witness_record<'g>(
        &self,
        graph: &'g Graph,
        anchor: NodeRef,
    ) -> Result<Option<&'g UniversalWitness>, ValidationFailure> {
        let mut result = None;
        for record in &graph.universal_witnesses {
            self.tick()?;
            if record.anchor == anchor {
                if result.is_some()
                    || record.ordinal > 1
                    || record.caller != self.current_context(graph)
                {
                    return Err("数値補完証拠のordinal・実Context・anchorが違う".into());
                }
                result = Some(record);
            }
        }
        Ok(result)
    }

    fn universal_active_witness(
        &self,
        graph: &Graph,
        record: &UniversalWitness,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let mut latest = None;
        for candidate in &graph.universal_witnesses {
            self.tick()?;
            if candidate.caller == record.caller
                && candidate.template == record.template
                && candidate.anchor.0 < limit
                && latest.is_none_or(|index| candidate.anchor.0 > index)
            {
                latest = Some(candidate.anchor.0);
            }
        }
        if latest != Some(record.anchor.0) {
            return Err("数値補完の現在producerが当該prefixの実anchorと違う".into());
        }
        Ok(())
    }

    fn universal_witness_expected(
        &self,
        graph: &Graph,
        record: &UniversalWitness,
        limit: usize,
    ) -> Result<WitnessReconstruction<WitnessSources>, ValidationFailure> {
        let (plan, domains, mut analysis) =
            self.universal_reanalysis(graph, record.template, limit)?;
        analysis.analysis.scope.completions = true;
        let classification = analysis
            .classification
            .as_ref()
            .ok_or("数値補完証拠の元アフィン分析がない")?;
        let pair = classification
            .completion_pair
            .as_ref()
            .ok_or("元式に成否を分ける数値補完対がない")?;
        let selected = if record.ordinal == 0 {
            &pair.0
        } else {
            &pair.1
        };
        let body = self.universal_body_producer(
            graph,
            record.template,
            &plan,
            record.anchor.0.min(limit),
        )?;
        self.recheck_evaluation(graph, body)?;
        let mut fields = BTreeMap::<Fact, NodeRef>::new();
        let reasons = self.universal_witness_reasons(
            graph,
            record.template,
            &plan,
            body,
            record.anchor.0.min(limit),
        )?;
        for reason in &reasons {
            self.tick()?;
            if !matches!(reason.kind, ReasonKind::Missing) {
                continue;
            }
            for fact in &reason.missing {
                self.tick()?;
                let field = self.field(
                    &fact.snapshot,
                    &fact.subject,
                    fact.field.as_deref().ok_or("数値補完理由に元fieldがない")?,
                )?;
                if matches!(field.ty, Type::Z | Type::Q) {
                    let source = *reason
                        .dependencies
                        .first()
                        .ok_or("数値補完の元欠測Sourceがない")?;
                    fields.entry(fact.clone()).or_insert(source);
                }
            }
        }
        let mut expected = Vec::new();
        for (fact, source) in fields {
            self.tick()?;
            let field = self.field(
                &fact.snapshot,
                &fact.subject,
                fact.field.as_deref().ok_or("数値補完fieldがない")?,
            )?;
            let value = selected
                .iter()
                .find(|(candidate, _)| candidate == &fact)
                .map(|(_, value)| value.clone())
                .unwrap_or_else(|| {
                    if field.ty == Type::Z {
                        Scalar::Z(0.into())
                    } else {
                        Scalar::Q(0.into(), 1.into())
                    }
                });
            if !matches!(field.slot, Slot::Missing) || value.ty() != field.ty {
                return Err("数値補完の元slot・型が違う".into());
            }
            expected.push((fact, value, source));
        }
        if selected
            .iter()
            .any(|(fact, _)| !expected.iter().any(|(actual, _, _)| actual == fact))
        {
            return Err("数値補完証拠が元欠測理由にないFactを使う".into());
        }
        Ok((expected, domains, analysis, body))
    }

    fn universal_validate_witness_anchor(
        &self,
        graph: &Graph,
        node: &Node,
        record: &UniversalWitness,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let mut prior = Vec::new();
        for candidate in &graph.universal_witnesses {
            self.tick()?;
            if candidate.caller == record.caller
                && candidate.template == record.template
                && candidate.anchor.0 < limit
            {
                prior.push(candidate.anchor);
            }
        }
        if prior.len() != record.ordinal {
            return Err("数値補完anchorの生成順と元ordinalが違う".into());
        }
        if let Some(&previous) = prior.first() {
            let mut completed = None;
            for (index, candidate) in graph.nodes.iter().enumerate().take(limit) {
                self.tick()?;
                if matches!(&candidate.payload,Some(Payload::Evaluation {expression,..}) if *expression==previous)
                {
                    if completed.is_some() {
                        return Err("数値補完の先行caseに複数のwhole producerがある".into());
                    }
                    completed = Some(NodeRef(index));
                }
            }
            self.recheck_evaluation(
                graph,
                completed.ok_or("数値補完の先行caseが未完成のまま次のanchorを作った")?,
            )?;
        }
        let (_, _, analysis, _) = self.universal_witness_expected(graph, record, limit)?;
        let template = graph.get(record.template)?;
        let Some(Payload::ParameterizedTransform {
            operation: TransformOp::Substitute,
            operands,
            parameters,
            bindings,
        }) = &node.payload
        else {
            return Err("数値補完anchorが既定identity代入でない".into());
        };
        let (_, fixed) = self.universal_source_fields(graph, record.template)?;
        let free = match &template.payload {
            Some(
                Payload::Expression { parameters, .. }
                | Payload::ParameterizedTransform { parameters, .. },
            ) => parameters,
            _ => return Err("数値補完anchorの元templateがない".into()),
        };
        if operands != &[record.template]
            || parameters != free
            || bindings != fixed
            || node.arguments
                != std::iter::once(record.template)
                    .chain(fixed.iter().map(|binding| binding.value))
                    .collect::<Vec<_>>()
            || !node.evidence.is_empty()
        {
            return Err("数値補完anchorの元式・自由軸・固定束縛が違う".into());
        }
        self.universal_metadata(
            node,
            template.ty.clone(),
            &analysis.analysis.scope,
            &analysis.analysis.support,
            &[],
            "expression",
        )
    }

    fn universal_witness_values(
        &self,
        graph: &Graph,
        record: &UniversalWitness,
        references: &[NodeRef],
        limit: usize,
    ) -> Result<WitnessReconstruction<Vec<(Fact, Scalar)>>, ValidationFailure> {
        let (expected, domains, analysis, body) =
            self.universal_witness_expected(graph, record, limit)?;
        if references.len() != expected.len() {
            return Err("数値補完証拠が全元missing Factを埋めていない".into());
        }
        let mut values = Vec::new();
        for (&reference, (fact, value, source)) in references.iter().zip(expected) {
            self.tick()?;
            let producer = graph.get(reference)?;
            if producer.arguments != [record.template, record.anchor, source]
                || graph.scalar(reference)? != &value
                || graph.context_at(reference.0) != record.caller
            {
                return Err("数値補完の値・元slot・anchor producerが違う".into());
            }
            self.validate_at(graph, producer, reference.0)?;
            values.push((fact, value));
        }
        Ok((values, domains, analysis, body))
    }

    fn universal_validate_witness_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if let Some(record) = self.universal_witness_record(graph, NodeRef(limit))? {
            self.universal_validate_witness_anchor(graph, node, record, limit)?;
            return Ok(true);
        }
        // 元ASTの各nodeも通る入口には、caseごとの再分析結果を確保しない。
        // 証拠の大型payloadは、実際に該当する枝の関数だけで保持する。
        match &node.payload {
            Some(Payload::Scalar(_)) => match node.arguments.get(1) {
                Some(&anchor) if self.universal_witness_record(graph, anchor)?.is_some() => {
                    self.universal_validate_witness_scalar(graph, node, limit)
                }
                _ => Ok(false),
            },
            Some(Payload::Evaluation { expression, .. })
                if self.universal_witness_record(graph, *expression)?.is_some() =>
            {
                self.universal_validate_witness_evaluation(graph, node, limit)
            }
            Some(Payload::CompletionPair { .. }) => {
                self.universal_validate_witness_pair(graph, node, limit)
            }
            _ => Ok(false),
        }
    }

    fn universal_validate_witness_scalar(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if let Some(Payload::Scalar(scalar)) = &node.payload {
            let Some(&anchor) = node.arguments.get(1) else {
                return Ok(false);
            };
            if let Some(record) = self.universal_witness_record(graph, anchor)? {
                self.universal_active_witness(graph, record, limit)?;
                self.validate_at(graph, graph.get(anchor)?, anchor.0)?;
                if node.arguments.first() != Some(&record.template) {
                    return Err("数値補完Scalarの元templateが違う".into());
                }
                let (expected, _, analysis, _) =
                    self.universal_witness_expected(graph, record, limit)?;
                if scalar.ty() != Type::Bool {
                    if node.arguments.len() != 3 {
                        return Err("数値補完値の元slot辺数が違う".into());
                    }
                    let source = node.arguments[2];
                    let (_, value, _) = expected
                        .iter()
                        .find(|(_, _, candidate)| *candidate == source)
                        .ok_or("数値補完値に元missing Sourceがない")?;
                    if scalar != value || !node.evidence.is_empty() {
                        return Err("数値補完値が元アフィン分析からの証拠値と違う".into());
                    }
                    self.universal_metadata(
                        node,
                        NodeType::Value(scalar.ty()),
                        &analysis.analysis.scope,
                        &[],
                        &[],
                        "evaluation",
                    )?;
                } else {
                    let (values, domains, _, _) =
                        self.universal_witness_values(graph, record, &node.arguments[2..], limit)?;
                    let rebuilt = self.universal_completion_analysis(
                        graph,
                        record.template,
                        &domains,
                        &values,
                    )?;
                    if Some(scalar) != rebuilt.value.map(Scalar::Bool).as_ref()
                        || !node.evidence.is_empty()
                    {
                        return Err("数値補完の結果が元Fact再代入・全称判断と違う".into());
                    }
                    self.universal_metadata(
                        node,
                        NodeType::Value(Type::Bool),
                        &analysis.analysis.scope,
                        &analysis.analysis.support,
                        &[],
                        "evaluation",
                    )?;
                }
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn universal_validate_witness_evaluation(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if let Some(Payload::Evaluation {
            expression,
            bindings,
            parts,
            value,
            applicability,
        }) = &node.payload
            && let Some(record) = self.universal_witness_record(graph, *expression)?
        {
            self.universal_active_witness(graph, record, limit)?;
            self.validate_at(graph, graph.get(*expression)?, expression.0)?;
            let (expected, domains, analysis, body) =
                self.universal_witness_expected(graph, record, limit)?;
            let offset = 1 + domains.len() + 2;
            let values = node
                .arguments
                .get(offset..offset + expected.len())
                .ok_or("数値補完wholeの値列がない")?;
            let (values, _, _, _) = self.universal_witness_values(graph, record, values, limit)?;
            let rebuilt =
                self.universal_completion_analysis(graph, record.template, &domains, &values)?;
            let residual = *node
                .arguments
                .get(2 + domains.len())
                .ok_or("数値補完wholeの元差評価がない")?;
            self.recheck_evaluation(graph, residual)?;
            if bindings != self.universal_source_fields(graph, record.template)?.1
                || parts.len() != 1
                || parts[0].location
                    != (Location::Law {
                        span: self.expression_span(
                            graph,
                            self.universal_raw_body(graph, record.template)?,
                        )?,
                    })
                || parts[0].children != [body]
                || parts[0].residual != Some(residual)
                || parts[0].value != *value
                || graph.boolean(*value)? != rebuilt.value
                || *applicability != "applicable"
                || !node.evidence.is_empty()
                || node.arguments.get(1..1 + domains.len()) != Some(domains.as_slice())
                || node.arguments.get(1 + domains.len()) != Some(&body)
                || node.arguments.len() != offset + expected.len() + 1
                || node.arguments.last() != value.as_ref()
            {
                return Err("数値補完wholeの実producer・元式・再代入判断が違う".into());
            }
            let value = value.ok_or("数値補完wholeの判断が未確定")?;
            if graph.get(value)?.arguments
                != [record.template, record.anchor]
                    .into_iter()
                    .chain(
                        node.arguments[offset..offset + expected.len()]
                            .iter()
                            .copied(),
                    )
                    .collect::<Vec<_>>()
            {
                return Err("数値補完wholeのBoolが別case producer".into());
            }
            self.validate_at(graph, graph.get(value)?, value.0)?;
            let (_, fixed) = self.universal_source_fields(graph, record.template)?;
            let plan = self.universal_plan_at(graph, record.template, fixed)?;
            let reasons = self.universal_witness_reasons(
                graph,
                record.template,
                &plan,
                body,
                record.anchor.0,
            )?;
            self.universal_metadata(
                node,
                NodeType::Evaluation(Type::Bool),
                &analysis.analysis.scope,
                &analysis.analysis.support,
                &reasons,
                "evaluation",
            )?;
            return Ok(true);
        }
        Ok(false)
    }

    fn universal_validate_witness_pair(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if let Some(Payload::CompletionPair {
            fields,
            first,
            second,
            first_result,
            second_result,
        }) = &node.payload
        {
            let Some(&template) = node.arguments.first() else {
                return Ok(false);
            };
            if self.universal_source_root(graph, template)? != Some(template) {
                return Ok(false);
            }
            if node.arguments.len() < 5 {
                return Err("数値補完対の元case辺がない".into());
            }
            let anchor0 = node.arguments[1];
            let anchor1 = node.arguments[2];
            let record0 = self
                .universal_witness_record(graph, anchor0)?
                .ok_or("数値補完対のfirst anchorがない")?;
            let record1 = self
                .universal_witness_record(graph, anchor1)?
                .ok_or("数値補完対のsecond anchorがない")?;
            if record0.template != template
                || record1.template != template
                || record0.ordinal != 0
                || record1.ordinal != 1
                || anchor0 == anchor1
            {
                return Err("数値補完対のordinal・元caseが違う".into());
            }
            let (values0, domains, analysis, _) =
                self.universal_witness_values(graph, record0, first, limit)?;
            let (values1, _, _, _) =
                self.universal_witness_values(graph, record1, second, limit)?;
            let rebuilt0 =
                self.universal_completion_analysis(graph, template, &domains, &values0)?;
            let rebuilt1 =
                self.universal_completion_analysis(graph, template, &domains, &values1)?;
            if fields
                != &values0
                    .iter()
                    .map(|(fact, _)| fact.clone())
                    .collect::<Vec<_>>()
                || analysis.value.is_some()
                || rebuilt0.value.is_none()
                || rebuilt1.value.is_none()
                || rebuilt0.value == rebuilt1.value
                || node.arguments
                    != [template, anchor0, anchor1, *first_result, *second_result]
                        .into_iter()
                        .chain(first.iter().copied())
                        .chain(second.iter().copied())
                        .collect::<Vec<_>>()
                || !node.evidence.is_empty()
            {
                return Err("数値補完対の元Fact全列・実case・全称成否が違う".into());
            }
            for (result, anchor) in [(*first_result, anchor0), (*second_result, anchor1)] {
                self.recheck_evaluation(graph, result)?;
                if self.evaluation(graph, result)?.0 != anchor {
                    return Err("数値補完対が別producerの結果を消費した".into());
                }
            }
            self.universal_metadata(
                node,
                NodeType::Evidence,
                &analysis.analysis.scope,
                &analysis.analysis.support,
                &[],
                "evidence",
            )?;
            return Ok(true);
        }
        Ok(false)
    }
    fn universal_comparison_producer(
        &self,
        graph: &Graph,
        template: NodeRef,
        plan: &UniversalPlan,
        limit: usize,
    ) -> Result<(NodeRef, NodeRef, NodeRef), ValidationFailure> {
        let mut current = None;
        for (index, node) in graph.nodes.iter().enumerate().take(limit).rev() {
            self.tick()?;
            if let Some(Payload::Evaluation { expression, .. }) = &node.payload
                && graph.context_at(index) == graph.context_at(template.0)
                && matches!(&graph.get(*expression)?.payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==plan.template_span)
                && graph.get(*expression)?.arguments.first() == Some(&template)
            {
                current = Some(NodeRef(index));
                break;
            }
        }
        let mut current = current.ok_or("全域差に先行する元body評価がない")?;
        self.recheck_evaluation(graph, current)?;
        loop {
            self.tick()?;
            let Some(Payload::Evaluation {
                expression, parts, ..
            }) = &graph.get(current)?.payload
            else {
                return Err("全域比較producerがEvaluationでない".into());
            };
            if parts.len() != 1 {
                return Err("全域比較producerの元part数が違う".into());
            }
            let span = self.expression_span(graph, *expression)?;
            let id = *self
                .expressions
                .get(&span)
                .ok_or("全域比較producerの元ASTがない")?;
            let children = &parts[0].children;
            current = match &self.inputs.law().exprs[id].kind {
                ExprKind::Binary { op: BinOp::Eq, .. } if children.len() == 2 => {
                    return Ok((*expression, children[0], children[1]));
                }
                ExprKind::Group(_) | ExprKind::Quant { .. } if children.len() == 1 => children[0],
                ExprKind::Let { .. } if children.len() == 2 => children[1],
                ExprKind::Match { .. } if children.len() == 2 => children[1],
                ExprKind::If { .. } if children.len() == 3 => {
                    match graph.boolean(self.evaluation(graph, children[0])?.2)? {
                        Some(true) => children[1],
                        Some(false) => children[2],
                        None => return Err("全域比較の実選択If枝が未確定".into()),
                    }
                }
                ExprKind::Call { .. } if self.named_view(id)?.is_some() => {
                    *children.last().ok_or("全域比較callの実bodyがない")?
                }
                _ => return Err("全域比較の元終端producerがEqでない".into()),
            };
        }
    }

    fn universal_counterexample_source(
        &self,
        graph: &Graph,
        template: NodeRef,
        plan: &UniversalPlan,
        limit: usize,
    ) -> Result<NodeRef, ValidationFailure> {
        let mut current = self.universal_body_producer(graph, template, plan, limit)?;
        self.recheck_evaluation(graph, current)?;
        loop {
            self.tick()?;
            let Some(Payload::Evaluation {
                expression, parts, ..
            }) = &graph.get(current)?.payload
            else {
                return Err("全域反例の元body producerがEvaluationでない".into());
            };
            let span = self.expression_span(graph, *expression)?;
            let id = *self
                .expressions
                .get(&span)
                .ok_or("全域反例の元body ASTがない")?;
            if id == plan.body {
                if graph.context_at(expression.0) != graph.context_at(template.0)
                    || graph.get(*expression)?.arguments.first() != Some(&template)
                {
                    return Err("全域反例の元body Sourceが別実Context・templateに属す".into());
                }
                return Ok(*expression);
            }
            if !matches!(self.inputs.law().exprs[id].kind, ExprKind::Quant { .. })
                || parts.len() != 1
                || parts[0].children.len() != 1
            {
                return Err("全域反例の代入対象が元先頭全称列のbodyでない".into());
            }
            current = parts[0].children[0];
        }
    }
    fn universal_fixed_bindings(
        &self,
        graph: &Graph,
        request: &Request,
        bindings: &[Binding],
    ) -> Result<(), ValidationFailure> {
        if let Some(instance) = self.current_context(graph).instance {
            // 混在族では元の有限rowだけを固定し、残る数値軸をBindingにしない。
            // rowの実producer・直積member・宣言順は既存の元入力再構成で照合する。
            let (expected, _, _) = self.family_instance_inputs(graph, instance)?;
            if bindings != expected {
                return Err("全域rowの固定bindingが元有限instanceと違う".into());
            }
            return Ok(());
        }
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration())
            .ok_or("全域元Requestの宣言がない")?;
        let parameters = match &declaration.signature {
            Signature::Law { params, .. } | Signature::View { params, .. } => params,
            _ => return Err("全域元Requestの署名が違う".into()),
        };
        let fixed = parameters
            .iter()
            .filter(|parameter| {
                request
                    .arguments
                    .iter()
                    .any(|argument| argument.name == format!("bind.{}", parameter.name))
            })
            .collect::<Vec<_>>();
        if fixed.len() != bindings.len() {
            return Err("全域元Sourceの固定binding数がRequestと違う".into());
        }
        for (parameter, binding) in fixed.iter().zip(bindings) {
            self.tick()?;
            let selected = request
                .arguments
                .iter()
                .find(|argument| argument.name == format!("bind.{}", parameter.name))
                .ok_or("全域固定selectorがない")?;
            let Selector::Subject { snapshot, subject } = &selected.value else {
                return Err("全域固定selectorがsubjectでない".into());
            };
            let original = self.subject(snapshot, subject)?;
            if binding.name != parameter.name
                || binding.ty != parameter.ty.erase()
                || graph.scalar(binding.value)?
                    != &(Scalar::Subject {
                        snapshot: snapshot.clone(),
                        subject: subject.clone(),
                        entity: original.ty.clone(),
                    })
                || graph.context_at(binding.value.0) != self.current_context(graph)
            {
                return Err("全域元Sourceの固定binding・実subject producerが違う".into());
            }
            self.validate_at(graph, graph.get(binding.value)?, binding.value.0)?;
        }
        Ok(())
    }
    fn universal_domain_refs(
        &self,
        graph: &Graph,
        template: NodeRef,
        plan: &UniversalPlan,
        limit: usize,
    ) -> Result<Vec<NodeRef>, ValidationFailure> {
        let mut domains = Vec::new();
        for (index, node) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if matches!(node.payload, Some(Payload::TypeDomain { .. }))
                && node.arguments == [template]
            {
                domains.push(NodeRef(index));
            }
        }
        self.universal_check_domains(graph, template, &domains, plan)?;
        for &domain in &domains {
            self.validate_at(graph, graph.get(domain)?, domain.0)?;
        }
        Ok(domains)
    }

    fn universal_reanalysis(
        &self,
        graph: &Graph,
        template: NodeRef,
        limit: usize,
    ) -> Result<(UniversalPlan, Vec<NodeRef>, UniversalAnalysis), ValidationFailure> {
        let (_, bindings) = self.universal_source_fields(graph, template)?;
        let plan = self.universal_plan_at(graph, template, bindings)?;
        let domains = self.universal_domain_refs(graph, template, &plan, limit)?;
        let analysis = self.universal_analysis(graph, template, &domains, bindings)?;
        Ok((plan, domains, analysis))
    }

    fn universal_steps(
        &self,
        graph: &Graph,
        template: NodeRef,
        steps: &[NodeRef],
        analysis: &UniversalAnalysis,
        plan: &UniversalPlan,
    ) -> Result<(), ValidationFailure> {
        if analysis.guard_value == Some(false) {
            let guard = plan.guard.ok_or("全域false guardに元guardがない")?;
            if steps.len() != 1
                || self.expression_span(graph, steps[0])? != self.inputs.law().exprs[guard].span
            {
                return Err("全域非適用の固定logic stepsが違う".into());
            }
        } else if analysis.comparison.is_some() {
            let difference = *steps.first().ok_or("全域正規化に元differenceがない")?;
            if !matches!(
                &graph.get(difference)?.payload,
                Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Difference,
                    ..
                })
            ) || graph.get(difference)?.arguments.first() != Some(&template)
            {
                return Err("全域正規化の元difference producerが違う".into());
            }
            let concrete = analysis.value == Some(false)
                && analysis
                    .classification
                    .as_ref()
                    .is_some_and(|classification| classification.common_counterexample.is_some());
            if steps.len() != 1 + usize::from(concrete) {
                return Err("全域正規化の具体反例代入数が違う".into());
            }
            for step in steps.iter().skip(1) {
                if !matches!(
                    &graph.get(*step)?.payload,
                    Some(Payload::ParameterizedTransform {
                        operation: TransformOp::Substitute,
                        ..
                    })
                ) || self.universal_source_root(graph, *step)? != Some(template)
                {
                    return Err("全域正規化の元代入stepsが違う".into());
                }
                let Some(Payload::ParameterizedTransform { operands, .. }) =
                    &graph.get(*step)?.payload
                else {
                    unreachable!()
                };
                let original =
                    self.universal_counterexample_source(graph, template, plan, step.0)?;
                if operands != &[original] {
                    return Err("全域正規化の代入対象が元bodyの実producerでない".into());
                }
            }
        } else if !steps.is_empty() {
            return Err("全域非アフィン式へ架空の正規化stepsがある".into());
        }
        for &step in steps {
            self.tick()?;
            self.validate_at(graph, graph.get(step)?, step.0)?;
        }
        Ok(())
    }

    fn universal_local_header(
        &self,
        graph: &Graph,
        header: NodeRef,
    ) -> Result<Option<LocalQuantifier>, ValidationFailure> {
        let source = graph.get(header)?;
        let Some(template) = self.universal_source_root(graph, header)? else {
            return Ok(None);
        };
        if template == header {
            return Ok(None);
        }
        let (span, _) = self.universal_source_fields(graph, header)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(None);
        };
        let (_, fixed) = self.universal_source_fields(graph, template)?;
        let plan = self.universal_plan_at(graph, template, fixed)?;
        let domains = self.universal_domains_from(graph, source, template, &plan)?;
        let Some(parameter) =
            self.universal_local_parameter(graph, &plan, template, &domains, id)?
        else {
            return Ok(None);
        };
        Ok(Some(LocalQuantifier {
            template,
            plan,
            domains,
            parameter,
        }))
    }

    fn universal_local_domain(
        &self,
        graph: &Graph,
        header: NodeRef,
        limit: usize,
    ) -> Result<NodeRef, ValidationFailure> {
        let mut result = None;
        for (index, candidate) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if matches!(candidate.payload, Some(Payload::TypeDomain { .. }))
                && candidate.arguments == [header]
                && result.replace(NodeRef(index)).is_some()
            {
                return Err("局所全称binderの実型Domainが一意でない".into());
            }
        }
        let domain = result.ok_or("局所全称binderの実型Domainがない")?;
        self.validate_at(graph, graph.get(domain)?, domain.0)?;
        Ok(domain)
    }

    fn universal_validate_domain(
        &self,
        graph: &Graph,
        node: &Node,
        ty: &Type,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let template = *node
            .arguments
            .first()
            .ok_or("全域型Domainの元templateがない")?;
        self.validate_at(graph, graph.get(template)?, template.0)?;
        if let Some(local) = self.universal_local_header(graph, template)? {
            for candidate in graph.nodes.iter().take(limit) {
                self.tick()?;
                if matches!(candidate.payload, Some(Payload::TypeDomain { .. }))
                    && candidate.arguments == [template]
                {
                    return Err("局所全称型Domainに同じ元headerの先行producerがある".into());
                }
            }
            if node.arguments != [template]
                || *ty != local.parameter.kind.ty()
                || self.current_context(graph) != local.parameter.context
                || graph.context_at(template.0) != self.current_context(graph)
            {
                return Err("局所全称型Domainの元binder・型・Context・producerが違う".into());
            }
            return self.universal_input_metadata(
                node,
                local.parameter.binder,
                NodeType::Domain,
                &graph.get(template)?.scope,
                &[],
            );
        }
        let (_, bindings) = self.universal_source_fields(graph, template)?;
        let plan = self.universal_plan_at(graph, template, bindings)?;
        let prior = graph
            .nodes
            .iter()
            .take(limit)
            .filter(|candidate| {
                matches!(candidate.payload, Some(Payload::TypeDomain { .. }))
                    && candidate.arguments == [template]
            })
            .count();
        let parameter = plan
            .parameters
            .get(prior)
            .ok_or("全域型Domainに元binderがない")?;
        if node.arguments != [template]
            || *ty != parameter.kind.ty()
            || self.current_context(graph) != parameter.context
        {
            return Err("全域型Domainの型・順序・binder・Contextが違う".into());
        }
        self.universal_input_metadata(
            node,
            parameter.binder,
            NodeType::Domain,
            &graph.get(template)?.scope,
            &[],
        )
    }

    fn universal_validate_logic_transform(
        &self,
        graph: &Graph,
        node: &Node,
        operation: TransformOp,
        operands: &[NodeRef],
        parameters: &[(String, Type)],
        bindings: &[Binding],
    ) -> Result<(), ValidationFailure> {
        if operands.len() != operation.arity() {
            return Err("全域含意式のarityが違う".into());
        }
        let body = match operation {
            TransformOp::Not => match &graph.get(operands[0])?.payload {
                Some(Payload::Expression { .. }) => operands[0],
                Some(Payload::ParameterizedTransform {
                    operation: TransformOp::And,
                    operands: and,
                    ..
                }) if and.len() == 2 => match &graph.get(and[1])?.payload {
                    Some(Payload::ParameterizedTransform {
                        operation: TransformOp::Not,
                        operands: not,
                        ..
                    }) if not.len() == 1 => not[0],
                    _ => return Err("全域含意body否定が違う".into()),
                },
                _ => return Err("全域含意Notの元operandが違う".into()),
            },
            TransformOp::And => match &graph.get(operands[1])?.payload {
                Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Not,
                    operands: not,
                    ..
                }) if not.len() == 1 => not[0],
                _ => return Err("全域含意Andの元operandが違う".into()),
            },
            _ => return Err("全域logic transform種が違う".into()),
        };
        let (body_span, body_bindings) = self.universal_source_fields(graph, body)?;
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("全域含意元Requestがない")?;
        let body_id = *self
            .expressions
            .get(&body_span)
            .ok_or("全域含意元body ASTがない")?;
        let plan = self
            .universal_family_plan(graph, request, bindings)?
            .or(self.universal_quantifier_plan(graph, body_id, bindings)?)
            .ok_or("全域含意に元未束縛parameterがない")?;
        let guard = plan.guard.ok_or("全域含意に元guardがない")?;
        if body_span != plan.template_span || body_bindings != bindings {
            return Err("全域含意の元bodyが違う".into());
        }
        let expected_parameters = match &graph.get(body)?.payload {
            Some(Payload::Expression { parameters, .. }) => parameters,
            _ => return Err("全域含意bodyが元Sourceでない".into()),
        };
        if parameters != expected_parameters {
            return Err("全域含意の自由parameterが違う".into());
        }
        let body_analysis = self
            .universal_template_source_analysis(graph, &plan, body_span, bindings)?
            .analysis;
        let guard_analysis = self
            .universal_template_source_analysis(
                graph,
                &plan,
                self.inputs.law().exprs[guard].span,
                bindings,
            )?
            .analysis;
        let mut scope = body_analysis.scope.clone();
        scope.merge(&guard_analysis.scope);
        let guard_source = if operation == TransformOp::And {
            Some(operands[0])
        } else if let Some(Payload::ParameterizedTransform {
            operation: TransformOp::And,
            operands: and,
            ..
        }) = &graph.get(operands[0])?.payload
        {
            Some(and[0])
        } else {
            None
        };
        if let Some(guard_source) = guard_source
            && (self.expression_span(graph, guard_source)? != self.inputs.law().exprs[guard].span
                || self.universal_source_fields(graph, guard_source)?.1 != bindings)
        {
            return Err("全域含意の元guardが違う".into());
        }
        let support = if guard_source.is_none() {
            // 内側のnot(body)は、元bodyの観測支持を保持する。
            body_analysis.support
        } else {
            let mut support = guard_analysis.support;
            if guard_analysis.known_value != Some(Scalar::Bool(false)) {
                support.extend(body_analysis.support);
            }
            support.sort();
            support.dedup();
            support
        };
        if node.arguments
            != operands
                .iter()
                .copied()
                .chain(bindings.iter().map(|binding| binding.value))
                .collect::<Vec<_>>()
            || !node.evidence.is_empty()
        {
            return Err("全域含意の元operand辺が違う".into());
        }
        self.universal_metadata(
            node,
            NodeType::Expression(Type::Bool),
            &scope,
            &support,
            &[],
            "expression",
        )?;
        for &operand in operands {
            self.tick()?;
            if graph.context_at(operand.0) != self.current_context(graph) {
                return Err("全域含意のproducerが別Context".into());
            }
            self.validate_at(graph, graph.get(operand)?, operand.0)?;
        }
        Ok(())
    }

    fn universal_validate_difference(
        &self,
        graph: &Graph,
        node: &Node,
        operands: &[NodeRef],
        parameters: &[(String, Type)],
        bindings: &[Binding],
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let template = *node.arguments.first().ok_or("全域差の元templateがない")?;
        let (plan, domains, analysis) = self.universal_reanalysis(graph, template, limit)?;
        let (lhs, rhs) = analysis.comparison.ok_or("全域差に元比較がない")?;
        let ty = self
            .inputs
            .law()
            .expr_type(lhs)
            .ok_or("全域差元数値型がない")?
            .clone();
        let offset = 1 + domains.len();
        let children = node.arguments.get(offset..).ok_or("全域差の元左右がない")?;
        if children.len() != 2
            || operands.len() != 2
            || node.arguments.get(1..offset) != Some(domains.as_slice())
            || bindings != self.universal_source_fields(graph, template)?.1
        {
            return Err("全域差の元左右・束縛が違う".into());
        }
        let (comparison_source, left_producer, right_producer) =
            self.universal_comparison_producer(graph, template, &plan, limit)?;
        let comparison_span = self.expression_span(graph, comparison_source)?;
        if children != [left_producer, right_producer]
            || analysis
                .comparison_expression
                .is_none_or(|id| self.inputs.law().exprs[id].span != comparison_span)
        {
            return Err("全域差が最終比較の実producerを消費していない".into());
        }
        for ((&child, &operand), id) in children.iter().zip(operands).zip([lhs, rhs]) {
            self.tick()?;
            let (source, actual, _) = self.evaluation(graph, child)?;
            if source != operand
                || actual != self.universal_source_fields(graph, comparison_source)?.1
                || graph.context_at(child.0) != graph.context_at(comparison_source.0)
            {
                return Err("全域差の実左右producerが違う".into());
            }
            self.source_matches(graph, source, id)?;
            self.recheck_evaluation(graph, child)?;
        }
        let expected = match &graph.get(operands[0])?.payload {
            Some(Payload::Expression { parameters, .. }) => parameters,
            _ => return Err("全域差の元左Sourceがない".into()),
        };
        if parameters != expected || !node.evidence.is_empty() {
            return Err("全域差の自由軸・証拠が違う".into());
        }
        self.universal_metadata(
            node,
            NodeType::Expression(ty),
            &analysis.analysis.scope,
            &analysis.analysis.support,
            &[],
            "expression",
        )
    }

    fn universal_local_evaluation(
        &self,
        graph: &Graph,
        header: NodeRef,
        children: &[NodeRef],
        limit: usize,
        local: LocalQuantifier,
    ) -> Result<LocalEvaluation, ValidationFailure> {
        self.universal_pointwise_children(graph, header, children, limit)?;
        if children.len() != 1 {
            return Err("局所全称評価の元body数が違う".into());
        }
        let domain = self.universal_local_domain(graph, header, limit)?;
        let (span, bindings) = self.universal_source_fields(graph, header)?;
        let analysis = self
            .universal_source_analysis(
                graph,
                span,
                bindings,
                &local.plan,
                &local.domains,
                local.template,
            )?
            .analysis;
        let mut scope = graph.get(header)?.scope.clone();
        scope.merge(&graph.get(children[0])?.scope);
        Ok(LocalEvaluation {
            arguments: vec![header, domain, children[0]],
            analysis,
            scope,
        })
    }

    fn universal_validate_local_pointwise(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
        local: LocalQuantifier,
    ) -> Result<(), ValidationFailure> {
        let EvaluationPayload {
            expression,
            bindings,
            parts,
            value,
            applicability,
        } = evaluation_payload(node)?;
        if bindings != self.universal_source_fields(graph, expression)?.1
            || parts.len() != 1
            || parts[0].location
                != (Location::Law {
                    span: self.expression_span(graph, expression)?,
                })
            || parts[0].residual.is_some()
            || parts[0].value != value
            || applicability != "applicable"
            || !node.evidence.is_empty()
        {
            return Err("局所全称評価の元body・束縛・適用が違う".into());
        }
        let checked =
            self.universal_local_evaluation(graph, expression, &parts[0].children, limit, local)?;
        if node.arguments
            != checked
                .arguments
                .iter()
                .copied()
                .chain(value)
                .collect::<Vec<_>>()
            || value.map(|value| graph.scalar(value)).transpose()?
                != checked.analysis.known_value.as_ref()
        {
            return Err("局所全称評価の元値・Domain・body辺が違う".into());
        }
        if let Some(value) = value {
            if graph.get(value)?.arguments != checked.arguments {
                return Err("局所全称評価の値が別producerに属す".into());
            }
            self.validate_at(graph, graph.get(value)?, value.0)?;
        }
        self.evaluation_missing_reasons(
            graph,
            node,
            expression,
            &parts[0].children,
            checked.analysis.missing.as_ref(),
        )?;
        self.universal_metadata(
            node,
            NodeType::Evaluation(Type::Bool),
            &checked.scope,
            &checked.analysis.support,
            &node.reasons,
            "evaluation",
        )
    }

    fn universal_validate_pointwise(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let EvaluationPayload {
            expression,
            bindings,
            parts,
            value,
            applicability,
        } = evaluation_payload(node)?;
        let source = graph.get(expression)?;
        self.validate_at(graph, source, expression.0)?;
        if let Some(local) = self.universal_local_header(graph, expression)? {
            return self.universal_validate_local_pointwise(graph, node, limit, local);
        }
        let template = self
            .universal_source_root(graph, expression)?
            .ok_or("全域評価に元templateがない")?;
        let (_, fixed) = self.universal_source_fields(graph, template)?;
        let plan = self.universal_plan_at(graph, template, fixed)?;
        let domains = self.universal_domains_from(graph, source, template, &plan)?;
        let (span, original) = self.universal_source_fields(graph, expression)?;
        let analyzed = self
            .universal_source_analysis(graph, span, bindings, &plan, &domains, template)?
            .analysis;
        if bindings != original
            || parts.len() != 1
            || parts[0].location != (Location::Law { span })
            || parts[0].residual.is_some()
            || parts[0].value != value
            || applicability != "applicable"
            || !node.evidence.is_empty()
        {
            return Err("全域各出現の評価・束縛・適用が違う".into());
        }
        let children = &parts[0].children;
        self.universal_pointwise_children(graph, expression, children, limit)?;
        let mut scope = source.scope.clone();
        for child in children {
            self.tick()?;
            scope.merge(&graph.get(*child)?.scope);
        }
        let expected = std::iter::once(expression)
            .chain(children.iter().copied())
            .chain(value)
            .collect::<Vec<_>>();
        if node.arguments != expected
            || value.map(|value| graph.scalar(value)).transpose()? != analyzed.known_value.as_ref()
        {
            return Err("全域各出現の元値・辺が違う".into());
        }
        if let Some(value) = value {
            let scalar = graph.get(value)?;
            if scalar.arguments
                != std::iter::once(expression)
                    .chain(children.iter().copied())
                    .collect::<Vec<_>>()
            {
                return Err("全域各出現の値producerが違う".into());
            }
            self.validate_at(graph, scalar, value.0)?;
        }
        self.evaluation_missing_reasons(
            graph,
            node,
            expression,
            children,
            analyzed.missing.as_ref(),
        )?;
        self.universal_metadata(
            node,
            NodeType::Evaluation(match &source.ty {
                NodeType::Expression(ty) => ty.clone(),
                _ => return Err("全域Sourceの型がExpressionでない".into()),
            }),
            &scope,
            &analyzed.support,
            &node.reasons,
            "evaluation",
        )
    }

    fn universal_validate_substitute(
        &self,
        graph: &Graph,
        node: &Node,
        operands: &[NodeRef],
        parameters: &[(String, Type)],
        bindings: &[Binding],
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        if operands.len() != 1 {
            return Err("全域代入の元operand数が違う".into());
        }
        let original = operands[0];
        self.validate_at(graph, graph.get(original)?, original.0)?;
        let template = self
            .universal_source_root(graph, original)?
            .ok_or("全域代入の元templateがない")?;
        let (plan, domains, _) = self.universal_reanalysis(graph, template, limit)?;
        let expected =
            self.universal_counterexample_bindings(graph, original, template, &domains)?;
        let (_, fixed) = self.universal_source_fields(graph, original)?;
        if bindings.len() != fixed.len() + expected.len()
            || bindings.get(..fixed.len()) != Some(fixed)
        {
            return Err("全域代入の元固定binding・代入数が違う".into());
        }
        let caller_body = self.universal_counterexample_source(graph, template, &plan, limit)?;
        let caller_values = if graph.context_at(original.0) == graph.context_at(caller_body.0) {
            self.universal_counterexample_bindings(graph, caller_body, template, &domains)?
        } else {
            Vec::new()
        };
        for (binding, (name, ty, value, binder)) in bindings[fixed.len()..].iter().zip(&expected) {
            self.tick()?;
            // 実Contextと元binderを含む同一代入だけcallerのScalarを共有する。
            // 局所binder・別callee formalは各実Sourceを起点に生成する。
            let binding_source =
                if caller_values.contains(&(name.clone(), ty.clone(), value.clone(), *binder)) {
                    caller_body
                } else {
                    original
                };
            let producer = graph.get(binding.value)?;
            if binding.name != *name
                || binding.ty != *ty
                || graph.scalar(binding.value)? != value
                || producer.arguments != [template, binding_source]
                || !matches!(&producer.rule,Rule::Input {kind:"law",location:Location::Law {span}} if span==binder)
                || graph.context_at(binding.value.0) != self.current_context(graph)
            {
                return Err("全域代入の型付きparameter・binder・値・producerが違う".into());
            }
            self.validate_at(graph, producer, binding.value.0)?;
        }
        let analyzed =
            self.universal_substitution_analysis(graph, original, bindings, template, &domains)?;
        if parameters != analyzed.parameters
            || node.arguments
                != std::iter::once(original)
                    .chain(bindings.iter().map(|binding| binding.value))
                    .collect::<Vec<_>>()
            || !node.evidence.is_empty()
        {
            return Err("全域代入の残自由parameter・元binding辺が違う".into());
        }
        self.universal_metadata(
            node,
            graph.get(original)?.ty.clone(),
            &analyzed.analysis.scope,
            &analyzed.analysis.support,
            &[],
            "expression",
        )
    }

    fn universal_substitute_analysis(
        &self,
        graph: &Graph,
        expression: NodeRef,
        limit: usize,
    ) -> Result<(NodeRef, UniversalSourceAnalysis), ValidationFailure> {
        let Some(Payload::ParameterizedTransform {
            operation: TransformOp::Substitute,
            operands,
            bindings,
            ..
        }) = &graph.get(expression)?.payload
        else {
            return Err("全域代入評価の元式が代入でない".into());
        };
        let original = *operands.first().ok_or("全域代入評価の元operandがない")?;
        let template = self
            .universal_source_root(graph, original)?
            .ok_or("全域代入評価の元templateがない")?;
        let (_, domains, _) = self.universal_reanalysis(graph, template, limit)?;
        Ok((
            original,
            self.universal_substitution_analysis(graph, original, bindings, template, &domains)?,
        ))
    }

    fn universal_validate_substitute_evaluation(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let EvaluationPayload {
            expression,
            bindings,
            parts,
            value,
            applicability,
        } = evaluation_payload(node)?;
        self.validate_at(graph, graph.get(expression)?, expression.0)?;
        let (original, analyzed) = self.universal_substitute_analysis(graph, expression, limit)?;
        let Some(Payload::ParameterizedTransform {
            bindings: expected, ..
        }) = &graph.get(expression)?.payload
        else {
            unreachable!()
        };
        if bindings != expected
            || parts.len() != 1
            || parts[0].children.len() != 1
            || parts[0].residual.is_some()
            || parts[0].value != value
            || applicability != "applicable"
            || !node.evidence.is_empty()
        {
            return Err("全域代入評価の元part・bindingが違う".into());
        }
        let child = parts[0].children[0];
        self.recheck_evaluation(graph, child)?;
        if self.evaluation(graph, child)?.0 != original
            || parts[0].location
                != (Location::Law {
                    span: self.expression_span(graph, original)?,
                })
            || node.arguments
                != [expression, child]
                    .into_iter()
                    .chain(value)
                    .collect::<Vec<_>>()
            || value.map(|value| graph.scalar(value)).transpose()?
                != analyzed.analysis.known_value.as_ref()
        {
            return Err("全域代入評価の元producer・型付き再代入値が違う".into());
        }
        if let Some(value) = value {
            if graph.get(value)?.arguments != [expression, child] {
                return Err("全域再代入値の実producerが違う".into());
            }
            self.validate_at(graph, graph.get(value)?, value.0)?;
        }
        let ty = match &graph.get(original)?.ty {
            NodeType::Expression(ty) => ty.clone(),
            _ => return Err("全域再代入の元型がない".into()),
        };
        self.universal_metadata(
            node,
            NodeType::Evaluation(ty),
            &analyzed.analysis.scope,
            &analyzed.analysis.support,
            &graph.get(child)?.reasons,
            "evaluation",
        )
    }

    fn universal_validate_difference_evaluation(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let EvaluationPayload {
            expression,
            bindings,
            parts,
            value,
            applicability,
        } = evaluation_payload(node)?;
        let difference = graph.get(expression)?;
        self.validate_at(graph, difference, expression.0)?;
        let template = *difference
            .arguments
            .first()
            .ok_or("全域差評価のtemplateがない")?;
        let (plan, domains, analysis) = self.universal_reanalysis(graph, template, limit)?;
        let children = difference
            .arguments
            .get(1 + domains.len()..)
            .ok_or("全域差評価に元左右がない")?;
        let comparison = analysis
            .comparison_expression
            .ok_or("全域差評価の元Eqがない")?;
        let span = self.inputs.law().exprs[comparison].span;
        let classification = analysis
            .classification
            .as_ref()
            .ok_or("全域差評価の元アフィン正規形がない")?;
        let known = classification.difference.value(&self.control)?;
        if bindings != self.universal_source_fields(graph, template)?.1
            || parts.len() != 1
            || parts[0].location != (Location::Law { span })
            || parts[0].value != value
            || parts[0].residual.is_some()
            || parts[0].children != children
            || applicability != "applicable"
            || !node.evidence.is_empty()
            || node.arguments
                != std::iter::once(expression)
                    .chain(children.iter().copied())
                    .chain(value)
                    .collect::<Vec<_>>()
            || value.map(|value| graph.scalar(value)).transpose()? != known.as_ref()
        {
            return Err("全域差の型付き残差・元子・値が違う".into());
        }
        let mut reasons = Vec::new();
        for &child in children {
            self.tick()?;
            self.recheck_evaluation(graph, child)?;
            reasons.extend(graph.get(child)?.reasons.iter().cloned());
        }
        sort_reasons(&mut reasons);
        if let Some(value) = value {
            self.validate_at(graph, graph.get(value)?, value.0)?;
        }
        let _ = plan;
        let ty = match &difference.ty {
            NodeType::Expression(ty) => ty.clone(),
            _ => return Err("全域残差の元数値型がない".into()),
        };
        self.universal_metadata(
            node,
            NodeType::Evaluation(ty),
            &analysis.analysis.scope,
            &analysis.analysis.support,
            &reasons,
            "evaluation",
        )
    }

    fn universal_validate_whole(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let EvaluationPayload {
            expression: template,
            bindings,
            parts,
            value,
            applicability,
        } = evaluation_payload(node)?;
        self.validate_at(graph, graph.get(template)?, template.0)?;
        let (plan, domains, analysis) = self.universal_reanalysis(graph, template, limit)?;
        if bindings != self.universal_source_fields(graph, template)?.1
            || parts.len() != 1 + usize::from(plan.guard.is_some())
        {
            return Err("全域wholeの元束縛・part数が違う".into());
        }
        let mut children = Vec::new();
        let mut reasons = Vec::new();
        if let Some(guard) = plan.guard {
            let part = &parts[0];
            if part.location
                != (Location::Law {
                    span: self.inputs.law().exprs[guard].span,
                })
                || part.children.len() != 1
                || part.residual.is_some()
            {
                return Err("全域wholeの元guard出現が違う".into());
            }
            let child = part.children[0];
            let (source, actual, guard_value) = self.evaluation(graph, child)?;
            self.source_matches(graph, source, guard)?;
            if actual != bindings
                || guard_value != part.value
                || graph.context_at(child.0) != self.current_context(graph)
            {
                return Err("全域wholeの実guard producerが違う".into());
            }
            self.recheck_evaluation(graph, child)?;
            children.push(child);
            reasons.extend(graph.get(child)?.reasons.iter().cloned());
        }
        let body = parts.last().ok_or("全域wholeの元body partがない")?;
        if body.location
            != (Location::Law {
                span: plan.template_span,
            })
        {
            return Err("全域wholeの元body出現が違う".into());
        }
        if analysis.guard_value == Some(false) {
            if body.value.is_some() || body.residual.is_some() || !body.children.is_empty() {
                return Err("全域非適用のbodyを評価済みにした".into());
            }
        } else {
            if body.children.len() != 1 {
                return Err("全域wholeに元bodyの実評価がない".into());
            }
            let child = body.children[0];
            let (source, actual, body_value) = self.evaluation(graph, child)?;
            if self.expression_span(graph, source)? != plan.template_span
                || actual != bindings
                || graph.context_at(child.0) != self.current_context(graph)
                || body.value
                    != if plan.guard.is_some() {
                        body_value
                    } else {
                        value
                    }
            {
                return Err("全域wholeの実body producer・値が違う".into());
            }
            self.recheck_evaluation(graph, child)?;
            children.push(child);
            reasons.extend(graph.get(child)?.reasons.iter().cloned());
            if analysis.comparison.is_some() != body.residual.is_some() {
                return Err("全域wholeの数値差を省略・捏造した".into());
            }
            if let Some(residual) = body.residual {
                self.recheck_evaluation(graph, residual)?;
                let difference = self.evaluation(graph, residual)?.0;
                if graph.get(difference)?.arguments.first() != Some(&template) {
                    return Err("全域wholeの残差が別templateに属す".into());
                }
            }
        }
        sort_reasons(&mut reasons);
        if analysis.value.is_none()
            && (analysis.classification.is_none()
                || (plan.guard.is_some() && analysis.guard_value.is_none()))
        {
            let mut operand_types = plan
                .parameters
                .iter()
                .map(|parameter| parameter.kind.ty())
                .collect::<Vec<_>>();
            operand_types.dedup();
            let request = graph
                .requests
                .get(self.current_context(graph).request)
                .ok_or("全域非対応算法の元Requestがない")?;
            reasons.push(Reason {
                kind: ReasonKind::UnsupportedAlgorithm {
                    question: request.kind,
                    operand_types,
                    method: if plan.guard.is_some() && analysis.guard_value.is_none() {
                        "parameter-dependent conditional affine equality"
                    } else {
                        "non-affine universal equality"
                    }
                    .into(),
                },
                request: request.id.clone(),
                dependencies: vec![template],
                missing: vec![],
                location: Some(Location::Law {
                    span: plan.template_span,
                }),
            });
            sort_reasons(&mut reasons);
        }
        let expected_applicability = if plan.guard.is_none() || analysis.guard_value == Some(true) {
            "applicable"
        } else if analysis.guard_value == Some(false) {
            "not_applicable"
        } else {
            "undetermined"
        };
        if applicability != expected_applicability || graph.boolean(value)? != analysis.value {
            return Err("全域wholeの適用・全補完判断が元式と違う".into());
        }
        let normalization = if let Some(value) = value {
            self.validate_at(graph, graph.get(value)?, value.0)?;
            if node.evidence.len() != 1 {
                return Err("全域wholeに正規化証拠がない".into());
            }
            let normalization = node.evidence[0];
            self.validate_at(graph, graph.get(normalization)?, normalization.0)?;
            if !matches!(&graph.get(normalization)?.payload,Some(Payload::Normalization {before,after,..}) if *before==template&&*after==value)
            {
                return Err("全域wholeの正規化が別producer".into());
            }
            Some(normalization)
        } else {
            let pair_expected = (plan.guard.is_none() || analysis.guard_value == Some(true))
                && analysis
                    .classification
                    .as_ref()
                    .is_some_and(|classification| classification.completion_pair.is_some());
            if pair_expected {
                if node.evidence.len() != 1 {
                    return Err("全域未決の補完対証拠がない".into());
                }
                let pair = node.evidence[0];
                if !matches!(
                    graph.get(pair)?.payload,
                    Some(Payload::CompletionPair { .. })
                ) || graph.get(pair)?.arguments.first() != Some(&template)
                {
                    return Err("全域未決の補完対が別元式に属す".into());
                }
                self.validate_at(graph, graph.get(pair)?, pair.0)?;
                Some(pair)
            } else {
                if !node.evidence.is_empty() {
                    return Err("全域未決に架空の証拠がある".into());
                }
                None
            }
        };
        let expected = std::iter::once(template)
            .chain(domains)
            .chain(children)
            .chain(body.residual)
            .chain(value)
            .chain(normalization)
            .collect::<Vec<_>>();
        if node.arguments != expected {
            return Err("全域wholeの元依存・残差・証拠順が違う".into());
        }
        self.universal_metadata(
            node,
            NodeType::Evaluation(Type::Bool),
            &analysis.analysis.scope,
            &analysis.analysis.support,
            &reasons,
            "evaluation",
        )
    }

    fn universal_validate_scalar(
        &self,
        graph: &Graph,
        node: &Node,
        scalar: &Scalar,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let Some(&first) = node.arguments.first() else {
            return Ok(false);
        };
        let Some(template) = self.universal_source_root(graph, first)? else {
            return Ok(false);
        };
        // 各元AST Scalarが通る入口は参照だけを持つ。証拠や正規形の大型値は
        // 該当する生産規則の関数に入ってから確保する。
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            if first == template {
                if matches!(node.rule, Rule::Input { kind: "law", .. }) {
                    self.universal_validate_parameter_scalar(graph, node, scalar, limit, template)
                } else {
                    self.universal_validate_whole_scalar(graph, node, scalar, limit, template)
                }
            } else {
                match &graph.get(first)?.payload {
                    Some(Payload::Expression { .. }) => self.universal_validate_pointwise_scalar(
                        graph, node, scalar, limit, first, template,
                    ),
                    Some(Payload::ParameterizedTransform {
                        operation: TransformOp::Difference,
                        ..
                    }) => self.universal_validate_difference_scalar(
                        graph, node, scalar, limit, first, template,
                    ),
                    Some(Payload::ParameterizedTransform {
                        operation: TransformOp::Substitute,
                        ..
                    }) => {
                        self.universal_validate_substitute_scalar(graph, node, scalar, limit, first)
                    }
                    _ => Ok(false),
                }
            }
        })
    }

    fn universal_parameter_scalar_producer(
        &self,
        graph: &Graph,
        template: NodeRef,
        plan: &UniversalPlan,
        domains: &[NodeRef],
        limit: usize,
    ) -> Result<ParameterScalarProducer, ValidationFailure> {
        let body = self.universal_counterexample_source(graph, template, plan, limit)?;
        let (_, left, right) = self.universal_comparison_producer(graph, template, plan, limit)?;
        let left = self.evaluation(graph, left)?.0;
        let right = self.evaluation(graph, right)?.0;
        let caller = self.universal_counterexample_bindings(graph, body, template, domains)?;
        let mut producers = Vec::new();
        for source in [body, left, right] {
            self.tick()?;
            let values =
                self.universal_counterexample_bindings(graph, source, template, domains)?;
            for binding in values {
                self.tick()?;
                if source != body
                    && graph.context_at(source.0) == graph.context_at(body.0)
                    && caller.contains(&binding)
                {
                    continue;
                }
                producers.push(ParameterScalarProducer {
                    source,
                    ty: binding.1,
                    value: binding.2,
                    binder: binding.3,
                });
            }
        }
        let mut ordinal = 0;
        for (index, candidate) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if matches!(candidate.payload, Some(Payload::Scalar(_)))
                && matches!(candidate.rule, Rule::Input { kind: "law", .. })
                && candidate.arguments.first() == Some(&template)
            {
                self.validate_at(graph, candidate, index)?;
                ordinal += 1;
            }
        }
        producers
            .into_iter()
            .nth(ordinal)
            .ok_or_else(|| "全域具体parameter Scalarが元caller/左右の生成列を超える".into())
    }

    fn universal_validate_parameter_scalar(
        &self,
        graph: &Graph,
        node: &Node,
        scalar: &Scalar,
        limit: usize,
        template: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        if node.arguments.len() != 2 {
            return Err("全域具体parameter Scalarの元辺数が違う".into());
        }
        let original = node.arguments[1];
        let (plan, domains, analysis) = self.universal_reanalysis(graph, template, limit)?;
        let expected =
            self.universal_parameter_scalar_producer(graph, template, &plan, &domains, limit)?;
        let Rule::Input {
            location: Location::Law { span },
            ..
        } = &node.rule
        else {
            return Err("全域具体parameterに元binderがない".into());
        };
        if original != expected.source
            || scalar.ty() != expected.ty
            || scalar != &expected.value
            || *span != expected.binder
            || self.current_context(graph) != graph.context_at(template.0)
        {
            return Err("全域具体parameterの元binder・型付き値・実producer順が違う".into());
        }
        self.universal_input_metadata(
            node,
            *span,
            NodeType::Value(scalar.ty()),
            &analysis.analysis.scope,
            &analysis.analysis.support,
        )?;
        Ok(true)
    }

    fn universal_validate_local_scalar(
        &self,
        graph: &Graph,
        node: &Node,
        scalar: &Scalar,
        limit: usize,
        header: NodeRef,
        local: LocalQuantifier,
    ) -> Result<bool, ValidationFailure> {
        let children = node
            .arguments
            .get(2..)
            .ok_or("局所全称Scalarの元bodyがない")?;
        let checked = self.universal_local_evaluation(graph, header, children, limit, local)?;
        if node.arguments != checked.arguments
            || checked.analysis.known_value.as_ref() != Some(scalar)
        {
            return Err("局所全称Scalarの値・Domain・実bodyが違う".into());
        }
        self.universal_input_metadata(
            node,
            self.expression_span(graph, header)?,
            NodeType::Value(scalar.ty()),
            &checked.scope,
            &checked.analysis.support,
        )?;
        Ok(true)
    }

    fn universal_validate_pointwise_scalar(
        &self,
        graph: &Graph,
        node: &Node,
        scalar: &Scalar,
        limit: usize,
        first: NodeRef,
        template: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let source = graph.get(first)?;
        self.validate_at(graph, source, first.0)?;
        if let Some(local) = self.universal_local_header(graph, first)? {
            return self.universal_validate_local_scalar(graph, node, scalar, limit, first, local);
        }
        let (span, bindings) = self.universal_source_fields(graph, first)?;
        let (_, fixed) = self.universal_source_fields(graph, template)?;
        let plan = self.universal_plan_at(graph, template, fixed)?;
        let domains = self.universal_domains_from(graph, source, template, &plan)?;
        let analysis = self
            .universal_source_analysis(graph, span, bindings, &plan, &domains, template)?
            .analysis;
        self.universal_pointwise_children(graph, first, &node.arguments[1..], limit)?;
        let mut scope = source.scope.clone();
        for child in &node.arguments[1..] {
            self.tick()?;
            scope.merge(&graph.get(*child)?.scope);
        }
        if analysis.known_value.as_ref() != Some(scalar) {
            return Err("全域出現のScalarが元入力の値と違う".into());
        }
        self.universal_input_metadata(
            node,
            span,
            NodeType::Value(scalar.ty()),
            &scope,
            &analysis.support,
        )?;
        Ok(true)
    }

    fn universal_validate_difference_scalar(
        &self,
        graph: &Graph,
        node: &Node,
        scalar: &Scalar,
        limit: usize,
        first: NodeRef,
        template: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let difference = graph.get(first)?;
        self.validate_at(graph, difference, first.0)?;
        let (_, domains, analysis) = self.universal_reanalysis(graph, template, limit)?;
        let expected = analysis
            .classification
            .as_ref()
            .ok_or("全域残差Scalarの元正規形がない")?
            .difference
            .value(&self.control)?;
        if expected.as_ref() != Some(scalar)
            || node.arguments
                != std::iter::once(first)
                    .chain(difference.arguments[1 + domains.len()..].iter().copied())
                    .collect::<Vec<_>>()
            || !node.evidence.is_empty()
        {
            return Err("全域残差Scalarの値・元左右が違う".into());
        }
        self.universal_metadata(
            node,
            NodeType::Value(scalar.ty()),
            &analysis.analysis.scope,
            &analysis.analysis.support,
            &[],
            "evaluation",
        )?;
        Ok(true)
    }

    fn universal_validate_substitute_scalar(
        &self,
        graph: &Graph,
        node: &Node,
        scalar: &Scalar,
        limit: usize,
        first: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        self.validate_at(graph, graph.get(first)?, first.0)?;
        let (original, analyzed) = self.universal_substitute_analysis(graph, first, limit)?;
        let child = *node
            .arguments
            .get(1)
            .ok_or("全域代入Scalarに実producerがない")?;
        if node.arguments.len() != 2
            || self.evaluation(graph, child)?.0 != original
            || analyzed.analysis.known_value.as_ref() != Some(scalar)
            || !node.evidence.is_empty()
        {
            return Err("全域代入Scalarの実producer・値が違う".into());
        }
        self.recheck_evaluation(graph, child)?;
        self.universal_metadata(
            node,
            NodeType::Value(scalar.ty()),
            &analyzed.analysis.scope,
            &analyzed.analysis.support,
            &[],
            "evaluation",
        )?;
        Ok(true)
    }

    fn universal_validate_whole_scalar(
        &self,
        graph: &Graph,
        node: &Node,
        scalar: &Scalar,
        limit: usize,
        template: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let (plan, _, analysis) = self.universal_reanalysis(graph, template, limit)?;
        if matches!(node.rule, Rule::Construction("proposition")) {
            if scalar != &Scalar::Bool(true) || node.arguments.len() != 3 {
                return Err("全域反証の比較先真値が違う".into());
            }
            let evaluation = node.arguments[1];
            let normalization = node.arguments[2];
            self.recheck_evaluation(graph, evaluation)?;
            self.validate_at(graph, graph.get(normalization)?, normalization.0)?;
            if self.evaluation(graph, evaluation)?.0 != template
                || analysis.value != Some(false)
                || graph.get(evaluation)?.evidence != [normalization]
            {
                return Err("全域反証の真値が別wholeに属す".into());
            }
            self.universal_metadata(
                node,
                NodeType::Value(Type::Bool),
                &analysis.analysis.scope,
                &[],
                &[],
                "proposition",
            )?;
        } else {
            self.universal_steps(graph, template, &node.arguments[1..], &analysis, &plan)?;
            if Some(scalar) != analysis.value.map(Scalar::Bool).as_ref()
                || !node.evidence.is_empty()
            {
                return Err("全域Boolが元全域判断と違う".into());
            }
            self.universal_metadata(
                node,
                NodeType::Value(Type::Bool),
                &analysis.analysis.scope,
                &analysis.analysis.support,
                &[],
                "evaluation",
            )?;
        }
        Ok(true)
    }

    fn universal_validate_normalization(
        &self,
        graph: &Graph,
        node: &Node,
        before: NodeRef,
        after: NodeRef,
        steps: &[NodeRef],
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        self.validate_at(graph, graph.get(before)?, before.0)?;
        let (plan, _, analysis) = self.universal_reanalysis(graph, before, limit)?;
        self.universal_steps(graph, before, steps, &analysis, &plan)?;
        self.validate_at(graph, graph.get(after)?, after.0)?;
        if analysis.value.is_none()
            || graph.boolean(Some(after))? != analysis.value
            || graph.get(after)?.arguments
                != std::iter::once(before)
                    .chain(steps.iter().copied())
                    .collect::<Vec<_>>()
            || node.arguments
                != [before, after]
                    .into_iter()
                    .chain(steps.iter().copied())
                    .collect::<Vec<_>>()
            || !node.evidence.is_empty()
        {
            return Err("全域normalizationの元式・steps・結果が違う".into());
        }
        self.universal_metadata(
            node,
            NodeType::Evidence,
            &analysis.analysis.scope,
            &analysis.analysis.support,
            &[],
            "evidence",
        )
    }

    fn universal_validate_counterexample(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let Some(Payload::Counterexample {
            bindings,
            left,
            right,
            facts,
        }) = &node.payload
        else {
            return Err("全域反例のpayloadがCounterexampleでない".into());
        };
        let (bindings, left, right, facts) = (bindings.as_slice(), *left, *right, facts.as_slice());
        let template = *node.arguments.first().ok_or("全域反例の元templateがない")?;
        let (plan, domains, analysis) = self.universal_reanalysis(graph, template, limit)?;
        if analysis
            .classification
            .as_ref()
            .is_some_and(|classification| classification.common_counterexample.is_some())
        {
            if node.arguments.len() != 5
                || analysis.value != Some(false)
                || facts != analysis.analysis.support
                || !node.evidence.is_empty()
            {
                return Err("全域具体反例の元導出・全域判断が違う".into());
            }
            let normalization = node.arguments[1];
            let substitute = node.arguments[2];
            if node.arguments[3..] != [left, right] {
                return Err("全域具体反例の実左右辺が違う".into());
            }
            self.validate_at(graph, graph.get(normalization)?, normalization.0)?;
            self.validate_at(graph, graph.get(substitute)?, substitute.0)?;
            let Some(Payload::Normalization { before, steps, .. }) =
                &graph.get(normalization)?.payload
            else {
                return Err("全域具体反例の正規化証拠がない".into());
            };
            if *before != template || steps.last() != Some(&substitute) {
                return Err("全域具体反例の正規化が別producer".into());
            }
            let Some(Payload::ParameterizedTransform {
                operation: TransformOp::Substitute,
                operands,
                bindings: actual,
                ..
            }) = &graph.get(substitute)?.payload
            else {
                return Err("全域具体反例の元Eq代入がない".into());
            };
            if actual != bindings || operands.len() != 1 {
                return Err("全域具体反例の型付き代入bindingが違う".into());
            }
            let original = operands[0];
            if original
                != self.universal_counterexample_source(graph, template, &plan, substitute.0)?
            {
                return Err("全域具体反例が元caller bodyの実producerへ代入していない".into());
            }
            let analyzed = self
                .universal_substitution_analysis(graph, original, bindings, template, &domains)?;
            if analyzed.analysis.known_value != Some(Scalar::Bool(false)) {
                return Err("全域具体反例を元Eqへ戻すと偽にならない".into());
            }
            let (lhs, rhs) = analysis.comparison.ok_or("全域具体反例の元左右ASTがない")?;
            let (comparison_source, original_left, original_right) =
                self.universal_comparison_producer(graph, template, &plan, substitute.0)?;
            let comparison_span = self.expression_span(graph, comparison_source)?;
            if analysis
                .comparison_expression
                .is_none_or(|id| self.inputs.law().exprs[id].span != comparison_span)
            {
                return Err("全域具体反例の元最終比較producerが違う".into());
            }
            for (evaluation, id, original_evaluation) in
                [(left, lhs, original_left), (right, rhs, original_right)]
            {
                self.tick()?;
                self.recheck_evaluation(graph, evaluation)?;
                let (expression, _, _) = self.evaluation(graph, evaluation)?;
                let Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Substitute,
                    operands,
                    ..
                }) = &graph.get(expression)?.payload
                else {
                    return Err("全域具体反例の左右が再代入評価でない".into());
                };
                let original_source = self.evaluation(graph, original_evaluation)?.0;
                let Some(Payload::Evaluation { parts, .. }) = &graph.get(evaluation)?.payload
                else {
                    unreachable!()
                };
                if operands != &[original_source]
                    || parts.len() != 1
                    || parts[0].children != [original_evaluation]
                {
                    return Err("全域具体反例の左右再代入が元最終比較の実producerと違う".into());
                }
                self.source_matches(graph, operands[0], id)?;
            }
            return self.universal_metadata(
                node,
                NodeType::Evidence,
                &analysis.analysis.scope,
                &analysis.analysis.support,
                &[],
                "evidence",
            );
        }
        if node.arguments.len() != 3
            || bindings != self.universal_source_fields(graph, template)?.1
            || analysis.value != Some(false)
            || facts != analysis.analysis.support
            || !node.evidence.is_empty()
        {
            return Err("全域反例の元束縛・全域反証・事実が違う".into());
        }
        let evaluation = node.arguments[1];
        let normalization = node.arguments[2];
        self.recheck_evaluation(graph, evaluation)?;
        self.validate_at(graph, graph.get(normalization)?, normalization.0)?;
        self.validate_at(graph, graph.get(right)?, right.0)?;
        if self.evaluation(graph, evaluation)?.0 != template
            || self.evaluation(graph, evaluation)?.2 != Some(left)
            || graph.boolean(Some(left))? != Some(false)
            || graph.boolean(Some(right))? != Some(true)
            || graph.get(evaluation)?.evidence != [normalization]
            || graph.get(right)?.arguments != node.arguments
        {
            return Err("全域反例の元whole・比較先producerが違う".into());
        }
        self.universal_metadata(
            node,
            NodeType::Evidence,
            &analysis.analysis.scope,
            &analysis.analysis.support,
            &[],
            "evidence",
        )
    }

    fn universal_validate_instance(
        &self,
        graph: &Graph,
        node: &Node,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::LawInstance {
            name,
            role,
            bindings,
            guard,
            body,
            occurrence,
        }) = &node.payload
        else {
            return Err("全域LawInstanceのpayloadが違う".into());
        };
        let (name, role, bindings, guard, body) =
            (name.as_str(), *role, bindings.as_slice(), *guard, *body);
        let Some(&evaluation) = node.arguments.first() else {
            return Ok(false);
        };
        let Ok((template, actual, _)) = self.evaluation(graph, evaluation) else {
            return Ok(false);
        };
        if self.universal_source_root(graph, template)? != Some(template) {
            return Ok(false);
        }
        self.recheck_evaluation(graph, evaluation)?;
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("全域LawInstance元Requestがない")?;
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration())
            .ok_or("全域LawInstance元宣言がない")?;
        let Signature::Law {
            body: original,
            guard: original_guard,
            role: original_role,
            ..
        } = &declaration.signature
        else {
            return Err("全域LawInstance元署名が違う".into());
        };
        let expected_role = match original_role {
            crate::law::ast::Role::Required => "required",
            crate::law::ast::Role::Optional => "optional",
        };
        if name != declaration.name
            || role != expected_role
            || actual != bindings
            || self.universal_raw_body(graph, template)? != body
            || *occurrence
                != (Location::Law {
                    span: declaration.span,
                })
            || self.expression_span(graph, body)? != self.inputs.law().exprs[*original].span
            || guard
                .map(|guard| self.expression_span(graph, guard))
                .transpose()?
                != original_guard.map(|guard| self.inputs.law().exprs[guard].span)
            || node.arguments
                != std::iter::once(evaluation)
                    .chain(bindings.iter().map(|binding| binding.value))
                    .collect::<Vec<_>>()
            || !node.evidence.is_empty()
        {
            return Err("全域LawInstanceの名前・role・元guard/body・束縛が違う".into());
        }
        let whole = graph.get(evaluation)?;
        self.universal_metadata(
            node,
            NodeType::LawInstance,
            &whole.scope,
            &whole.support,
            &[],
            "law_instance",
        )?;
        Ok(true)
    }

    fn universal_validate_claim(
        &self,
        graph: &Graph,
        node: &Node,
        instance: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let instance_node = graph.get(instance)?;
        let Some(&evaluation) = instance_node.arguments.first() else {
            return Ok(false);
        };
        let Ok((template, _, value)) = self.evaluation(graph, evaluation) else {
            return Ok(false);
        };
        if self.universal_source_root(graph, template)? != Some(template) {
            return Ok(false);
        }
        self.validate_at(graph, instance_node, instance.0)?;
        self.recheck_evaluation(graph, evaluation)?;
        let whole = graph.get(evaluation)?;
        let status = family::family_decision(graph.boolean(value)?);
        let judgment = node.judgment.as_ref().ok_or("全域命題の判断がない")?;
        if node.ty != NodeType::Proposition
            || node.arguments != [instance, evaluation]
            || node.scope != whole.scope
            || node.support != whole.support
            || !matches!(node.rule, Rule::Construction("proposition"))
            || !reasons_equal(&node.reasons, &whole.reasons)
            || judgment.status != status
            || judgment.evidence != node.evidence
            || !reasons_equal(&judgment.reasons, &whole.reasons)
        {
            return Err("全域命題の元Law・Scope・理由・判断が違う".into());
        }
        let (plan, _, analysis) = self.universal_reanalysis(graph, template, self.cutoff.get())?;
        let pair = analysis.value.is_none()
            && (plan.guard.is_none() || analysis.guard_value == Some(true))
            && analysis
                .classification
                .as_ref()
                .is_some_and(|classification| classification.completion_pair.is_some());
        if node.evidence.get(..whole.evidence.len()) != Some(whole.evidence.as_slice())
            || node.evidence.len()
                != whole.evidence.len() + usize::from(status == Decision::Refuted)
        {
            return Err("全域命題の正規化・反例証拠が違う".into());
        }
        for &evidence in &node.evidence {
            self.tick()?;
            self.validate_at(graph, graph.get(evidence)?, evidence.0)?;
        }
        if pair
            && (!matches!(
                graph.get(node.evidence[0])?.payload,
                Some(Payload::CompletionPair { .. })
            ) || graph.get(node.evidence[0])?.arguments.first() != Some(&template))
        {
            return Err("全域未決の補完対が元式と違う".into());
        }
        if status == Decision::Refuted {
            let counterexample = *node.evidence.last().ok_or("全域反証の反例がない")?;
            if !matches!(
                graph.get(counterexample)?.payload,
                Some(Payload::Counterexample { .. })
            ) || graph.get(counterexample)?.arguments.first() != Some(&template)
            {
                return Err("全域反証が別wholeの反例を消費している".into());
            }
        }
        Ok(true)
    }

    pub(in crate::observed) fn validate_universal_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        // 共通sessionと同じ保護を、分野別の検査frameを確保する前にも置く。
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.validate_universal_node_inner(graph, node, limit)
        })
    }

    fn validate_universal_node_inner(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        self.tick()?;
        if self.universal_validate_witness_node(graph, node, limit)? {
            return Ok(true);
        }
        if self.universal_validate_source(graph, node, limit)? {
            return Ok(true);
        }
        match &node.payload {
            Some(Payload::TypeDomain { ty }) => {
                self.universal_validate_domain(graph, node, ty, limit)?;
                return Ok(true);
            }
            Some(Payload::ParameterizedTransform {
                operation,
                operands,
                parameters,
                bindings,
            }) => {
                match operation {
                    TransformOp::Not | TransformOp::And => self
                        .universal_validate_logic_transform(
                            graph, node, *operation, operands, parameters, bindings,
                        )?,
                    TransformOp::Difference => self.universal_validate_difference(
                        graph, node, operands, parameters, bindings, limit,
                    )?,
                    TransformOp::Substitute => self.universal_validate_substitute(
                        graph, node, operands, parameters, bindings, limit,
                    )?,
                }
                return Ok(true);
            }
            Some(Payload::Scalar(scalar)) => {
                if self.universal_validate_scalar(graph, node, scalar, limit)? {
                    return Ok(true);
                }
            }
            Some(Payload::Evaluation { expression, .. }) => {
                if let Some(template) = self.universal_source_root(graph, *expression)? {
                    if template == *expression {
                        self.universal_validate_whole(graph, node, limit)?;
                    } else if matches!(
                        graph.get(*expression)?.payload,
                        Some(Payload::ParameterizedTransform {
                            operation: TransformOp::Difference,
                            ..
                        })
                    ) {
                        self.universal_validate_difference_evaluation(graph, node, limit)?;
                    } else {
                        if matches!(
                            graph.get(*expression)?.payload,
                            Some(Payload::ParameterizedTransform {
                                operation: TransformOp::Substitute,
                                ..
                            })
                        ) {
                            self.universal_validate_substitute_evaluation(graph, node, limit)?;
                            return Ok(true);
                        }
                        self.universal_validate_pointwise(graph, node, limit)?;
                    }
                    return Ok(true);
                }
            }
            Some(Payload::Normalization {
                before,
                after,
                steps,
            }) => {
                if self.universal_source_root(graph, *before)? == Some(*before) {
                    self.universal_validate_normalization(
                        graph, node, *before, *after, steps, limit,
                    )?;
                    return Ok(true);
                }
            }
            Some(Payload::Counterexample { .. }) => {
                if let Some(&template) = node.arguments.first()
                    && self.universal_source_root(graph, template)? == Some(template)
                {
                    self.universal_validate_counterexample(graph, node, limit)?;
                    return Ok(true);
                }
            }
            Some(Payload::LawInstance { .. }) => {
                if self.universal_validate_instance(graph, node)? {
                    return Ok(true);
                }
            }
            Some(Payload::Proposition { instance }) => {
                if self.universal_validate_claim(graph, node, *instance)? {
                    return Ok(true);
                }
            }
            _ => {}
        }
        // Scopeは実子から伝播する。内側に全称式を持つ通常のBool合成等は、
        // 上で識別した型Domain・固定変換・実templateの所有nodeとは区別し、
        // 既存経路で元AST・実子・値・支持・Domain付きScopeを照合する。
        Ok(false)
    }

    pub(in crate::observed) fn validate_universal_answer(
        &self,
        graph: &Graph,
        request: &Request,
        answer: &Answer,
    ) -> Result<bool, ValidationFailure> {
        let Some(&evaluation) = answer.outputs.get("evaluation") else {
            return Ok(false);
        };
        let (template, bindings, value) = self.evaluation(graph, evaluation)?;
        if self.universal_source_root(graph, template)? != Some(template) {
            return Ok(false);
        }
        let (_, _, analysis) = self.universal_reanalysis(graph, template, graph.nodes.len())?;
        self.recheck_evaluation(graph, evaluation)?;
        let whole = graph.get(evaluation)?;
        if answer.scope != whole.scope
            || !reasons_equal(&answer.reasons, &whole.reasons)
            || graph.boolean(value)? != analysis.value
        {
            return Err("全域Answerの元判断・Scope・理由が違う".into());
        }
        if request.kind == QuestionKind::Check {
            let claim = answer.claim.ok_or("全域check Answerに命題がない")?;
            self.validate_at(graph, graph.get(claim)?, claim.0)?;
            if graph.get(claim)?.arguments.get(1) != Some(&evaluation)
                || answer.outputs.get("proposition") != Some(&claim)
                || answer.status != family::family_decision(analysis.value)
                || answer.evidence != graph.get(claim)?.evidence
            {
                return Err("全域Answerの元命題・判断・証拠が違う".into());
            }
        } else if answer.claim.is_some()
            || answer.status
                != if value.is_some() {
                    Decision::Established
                } else {
                    Decision::Undetermined
                }
            || !answer.evidence.is_empty()
            || answer.outputs.get("value").copied() != value
        {
            return Err("全域値Answerの判断・証拠が違う".into());
        }
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration())
            .ok_or("全域Answer元宣言がない")?;
        let params = match &declaration.signature {
            Signature::Law { params, .. } | Signature::View { params, .. } => params,
            _ => return Err("全域Answer元署名が違う".into()),
        };
        let fixed = params
            .iter()
            .filter(|parameter| {
                request
                    .arguments
                    .iter()
                    .any(|argument| argument.name == format!("bind.{}", parameter.name))
            })
            .collect::<Vec<_>>();
        if fixed.len() != bindings.len() {
            return Err("全域Answerの固定束縛数が違う".into());
        }
        for (parameter, binding) in fixed.iter().zip(bindings) {
            self.tick()?;
            if parameter.name != binding.name || parameter.ty.erase() != binding.ty {
                return Err("全域Answer固定署名が違う".into());
            }
            let argument = request
                .arguments
                .iter()
                .find(|argument| argument.name == format!("bind.{}", parameter.name))
                .ok_or("全域Answer固定selectorがない")?;
            let Selector::Subject { snapshot, subject } = &argument.value else {
                return Err("全域Answer固定selectorがsubjectでない".into());
            };
            let original = self.subject(snapshot, subject)?;
            if graph.scalar(binding.value)?
                != &(Scalar::Subject {
                    snapshot: snapshot.clone(),
                    subject: subject.clone(),
                    entity: original.ty.clone(),
                })
                || graph.context_at(binding.value.0) != self.current_context(graph)
            {
                return Err("全域Answer固定subject・producerが違う".into());
            }
            self.validate_at(graph, graph.get(binding.value)?, binding.value.0)?;
        }
        Ok(true)
    }
    fn universal_source_fields<'g>(
        &self,
        graph: &'g Graph,
        source: NodeRef,
    ) -> Result<((usize, usize), &'g [Binding]), ValidationFailure> {
        match &graph.get(source)?.payload {
            Some(Payload::Expression {
                location: Location::Law { span },
                bindings,
                ..
            }) => Ok((*span, bindings)),
            Some(Payload::ParameterizedTransform { bindings, .. }) => {
                let raw = self.universal_raw_body(graph, source)?;
                Ok((self.expression_span(graph, raw)?, bindings))
            }
            _ => Err("全域の元Source・束縛がない".into()),
        }
    }

    fn universal_is_template(
        &self,
        graph: &Graph,
        reference: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let node = graph.get(reference)?;
        let Some(Payload::Expression {
            location: Location::Law { span },
            bindings,
            ..
        }) = &node.payload
        else {
            return Ok(matches!(
                node.payload,
                Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Not,
                    ..
                })
            ));
        };
        let Some(&id) = self.expressions.get(span) else {
            return Ok(false);
        };
        let Some(request) = self.universal_source_request(graph, *span, bindings)? else {
            return Ok(false);
        };
        if self.universal_finite_template(graph, request, *span, bindings)? {
            return Ok(false);
        }
        if let Some(declaration) = self.inputs.law().declarations.get(request.declaration())
            && let Signature::Law { body, .. } = &declaration.signature
            && self
                .universal_quantifier_plan(graph, *body, bindings)?
                .is_some_and(|plan| {
                    plan.template_span == *span
                        || plan
                            .guard
                            .is_some_and(|guard| self.inputs.law().exprs[guard].span == *span)
                })
        {
            return Ok(true);
        }
        if self
            .universal_family_plan(graph, request, bindings)?
            .is_some_and(|plan| {
                plan.template_span == *span
                    || plan
                        .guard
                        .is_some_and(|guard| self.inputs.law().exprs[guard].span == *span)
            })
        {
            return Ok(true);
        }
        Ok(self
            .universal_quantifier_plan(graph, id, bindings)?
            .is_some())
    }

    /// 旧来の通常SourceはRequest表を持たないGraphでも検査できる。
    /// 元数値binderのtemplateに該当するときだけ、新導出のRequestを必須にする。
    fn universal_source_request<'g>(
        &self,
        graph: &'g Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<Option<&'g Request>, ValidationFailure> {
        if let Some(request) = graph.requests.get(self.current_context(graph).request) {
            return Ok(Some(request));
        }
        if !graph.requests.is_empty() || self.universal_numeric_source(graph, span, bindings)? {
            return Err("全域の元numeric templateにRequestがない".into());
        }
        Ok(None)
    }

    fn universal_finite_template(
        &self,
        graph: &Graph,
        request: &Request,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<bool, ValidationFailure> {
        let context = self.current_context(graph);
        if context.instance.is_some() || context.frame.is_some() {
            return Ok(false);
        }
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration())
            .ok_or("全域/有限族の元宣言がない")?;
        let Signature::Law {
            params,
            body,
            guard,
            ..
        } = &declaration.signature
        else {
            return Ok(false);
        };
        if self.inputs.law().exprs[*body].span != span
            && guard.map(|guard| self.inputs.law().exprs[guard].span) != Some(span)
        {
            return Ok(false);
        }
        for parameter in params {
            self.tick()?;
            if !bindings
                .iter()
                .any(|binding| binding.name == parameter.name)
                && !matches!(parameter.ty, Type::Z | Type::Q)
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn universal_numeric_source(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<bool, ValidationFailure> {
        if let Some(&id) = self.expressions.get(&span)
            && self
                .universal_quantifier_plan(graph, id, bindings)?
                .is_some()
        {
            return Ok(true);
        }
        for declaration in self.inputs.law().declarations.values() {
            self.tick()?;
            if !(declaration.span.0 <= span.0 && span.1 <= declaration.span.1) {
                continue;
            }
            let Signature::Law {
                params,
                body,
                guard,
                ..
            } = &declaration.signature
            else {
                return Ok(false);
            };
            let guard_span = guard.map(|guard| self.inputs.law().exprs[guard].span);
            if self.inputs.law().exprs[*body].span != span && guard_span != Some(span) {
                return Ok(false);
            }
            let mut unbound = false;
            let mut all_numeric = true;
            for parameter in params {
                self.tick()?;
                if !bindings
                    .iter()
                    .any(|binding| binding.name == parameter.name)
                {
                    unbound = true;
                    all_numeric &= matches!(parameter.ty, Type::Z | Type::Q);
                }
            }
            if unbound && all_numeric {
                return Ok(true);
            }
            return Ok(guard_span == Some(span)
                && self
                    .universal_quantifier_plan(graph, *body, bindings)?
                    .is_some());
        }
        Ok(false)
    }

    pub(in crate::observed) fn universal_source_root(
        &self,
        graph: &Graph,
        source: NodeRef,
    ) -> Result<Option<NodeRef>, ValidationFailure> {
        let node = graph.get(source)?;
        match &node.payload {
            Some(Payload::Expression { .. }) => {
                if let Some(&first) = node.arguments.first()
                    && self.universal_is_template(graph, first)?
                {
                    return Ok(Some(first));
                }
                if self.universal_is_template(graph, source)? {
                    return Ok(Some(source));
                }
                Ok(None)
            }
            Some(Payload::ParameterizedTransform {
                operation: TransformOp::Difference,
                ..
            }) => Ok(node.arguments.first().copied()),
            Some(Payload::ParameterizedTransform {
                operation: TransformOp::Substitute,
                operands,
                ..
            }) => {
                let original = *operands.first().ok_or("全域代入に元operandがない")?;
                self.universal_source_root(graph, original)
            }
            Some(Payload::ParameterizedTransform { .. }) => Ok(Some(source)),
            _ => Ok(None),
        }
    }

    fn universal_metadata(
        &self,
        node: &Node,
        ty: NodeType,
        scope: &Scope,
        support: &[Fact],
        reasons: &[Reason],
        rule: &str,
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        if node.ty != ty
            || node.scope != *scope
            || node.support != support
            || !reasons_equal(&node.reasons, reasons)
            || !matches!(node.rule,Rule::Construction(actual) if actual==rule)
            || node.judgment.is_some()
        {
            return Err("全域nodeの型・Scope・支持・理由・構成が元入力と違う".into());
        }
        Ok(())
    }

    fn universal_input_metadata(
        &self,
        node: &Node,
        span: (usize, usize),
        ty: NodeType,
        scope: &Scope,
        support: &[Fact],
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        if node.ty != ty
            || node.scope != *scope
            || node.support != support
            || !node.reasons.is_empty()
            || !node.evidence.is_empty()
            || node.judgment.is_some()
            || !matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span:actual}} if *actual==span)
        {
            return Err("全域の元出現・型・Scope・支持が違う".into());
        }
        Ok(())
    }

    fn universal_domains_from(
        &self,
        graph: &Graph,
        node: &Node,
        template: NodeRef,
        plan: &UniversalPlan,
    ) -> Result<Vec<NodeRef>, ValidationFailure> {
        let domains = self.universal_source_domain_refs(graph, node, template, plan)?;
        for domain in &domains {
            self.tick()?;
            self.validate_at(graph, graph.get(*domain)?, domain.0)?;
        }
        Ok(domains)
    }

    fn universal_validate_source(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if !matches!(
            &node.payload,
            Some(Payload::Expression {
                location: Location::Law { .. },
                ..
            })
        ) {
            return Ok(false);
        }
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.universal_validate_source_inner(graph, node, limit)
        })
    }

    fn universal_validate_source_inner(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::Expression {
            location: Location::Law { span },
            parameters,
            bindings,
        }) = &node.payload
        else {
            return Ok(false);
        };
        let root = match node.arguments.first().copied() {
            Some(reference) if self.universal_is_template(graph, reference)? => Some(reference),
            _ => None,
        };
        let (analyzed, expected) = if let Some(template) = root {
            self.universal_pointwise_source_expectation(graph, node, *span, bindings, template)?
        } else {
            let Some(expected) = self.universal_raw_source_expectation(graph, *span, bindings)?
            else {
                // 全称子のScopeを継承したancestor Sourceは通常の元Source。
                // 元binderやtemplate辺を持たないだけで専用nodeとは判定しない。
                return Ok(false);
            };
            expected
        };
        if node.arguments != expected || *parameters != analyzed.parameters {
            return Err("全域Sourceの元引数・自由parameter順が違う".into());
        }
        let ty = if let Some(id) = self.expressions.get(span) {
            self.inputs
                .law()
                .expr_type(*id)
                .cloned()
                .ok_or("全域AST元型がない")?
        } else {
            let name = self.name_token(*span)?;
            bindings
                .iter()
                .find(|binding| binding.name == name)
                .map(|binding| binding.ty.clone())
                .or(self.call_parameter(graph, name)?.and_then(|reference| {
                    match &graph.get(reference).ok()?.ty {
                        NodeType::Evaluation(ty) => Some(ty.clone()),
                        _ => None,
                    }
                }))
                .ok_or("全域fragment元型がない")?
        };
        self.universal_input_metadata(
            node,
            *span,
            NodeType::Expression(ty),
            &analyzed.analysis.scope,
            &[],
        )?;
        for reference in &expected {
            self.tick()?;
            if reference.0 >= limit {
                return Err("全域Sourceの参照が未出".into());
            }
            self.validate_at(graph, graph.get(*reference)?, reference.0)?;
        }
        Ok(true)
    }

    fn universal_pointwise_source_expectation(
        &self,
        graph: &Graph,
        node: &Node,
        span: (usize, usize),
        bindings: &[Binding],
        template: NodeRef,
    ) -> Result<SourceExpectation, ValidationFailure> {
        self.validate_at(graph, graph.get(template)?, template.0)?;
        let (_, fixed) = self.universal_source_fields(graph, template)?;
        let plan = self.universal_plan_at(graph, template, fixed)?;
        let domains = self.universal_domains_from(graph, node, template, &plan)?;
        let analyzed =
            self.universal_source_analysis(graph, span, bindings, &plan, &domains, template)?;
        let arguments = std::iter::once(template)
            .chain(domains.iter().copied())
            .chain(self.source_arguments(graph, span, bindings)?)
            .collect();
        Ok((analyzed, arguments))
    }

    fn universal_raw_source_expectation(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<Option<SourceExpectation>, ValidationFailure> {
        let Some(request) = self.universal_source_request(graph, span, bindings)? else {
            return Ok(None);
        };
        if self.universal_finite_template(graph, request, span, bindings)? {
            return Ok(None);
        }
        let id = self.expressions.get(&span).copied();
        let matches_source = |plan: &UniversalPlan| {
            plan.template_span == span
                || plan
                    .guard
                    .is_some_and(|guard| self.inputs.law().exprs[guard].span == span)
        };
        let mut plan = self
            .universal_family_plan(graph, request, bindings)?
            .filter(matches_source)
            .or(id
                .map(|id| self.universal_quantifier_plan(graph, id, bindings))
                .transpose()?
                .flatten());
        if plan.is_none()
            && let Some(declaration) = self.inputs.law().declarations.get(request.declaration())
            && let Signature::Law { body, .. } = &declaration.signature
        {
            plan = self
                .universal_quantifier_plan(graph, *body, bindings)?
                .filter(matches_source);
        }
        let Some(plan) = plan else {
            return Ok(None);
        };
        if self.current_context(graph).frame.is_none() {
            self.universal_fixed_bindings(graph, request, bindings)?;
            let declaration = self
                .inputs
                .law()
                .declarations
                .get(request.declaration())
                .ok_or("全域Source元宣言がない")?;
            if !(declaration.span.0 <= span.0 && span.1 <= declaration.span.1) {
                return Err("全域Sourceの元ASTが別Request宣言に属す".into());
            }
        }
        let analyzed = self.universal_template_source_analysis(graph, &plan, span, bindings)?;
        Ok(Some((
            analyzed,
            self.source_arguments(graph, span, bindings)?,
        )))
    }

    fn universal_pointwise_children(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let (span, bindings) = self.universal_source_fields(graph, source)?;
        let Some(&id) = self.expressions.get(&span) else {
            let name = self.name_token(span)?;
            let expected = self.call_parameter(graph, name)?;
            if children != expected.into_iter().collect::<Vec<_>>() {
                return Err("全域fragmentの実producerが違う".into());
            }
            return Ok(());
        };
        let law = self.inputs.law();
        let ids = match &law.exprs[id].kind {
            ExprKind::Int(_) | ExprKind::Bool(_) => vec![],
            ExprKind::Field { base, .. }
            | ExprKind::Group(base)
            | ExprKind::Unary { operand: base, .. } => vec![*base],
            ExprKind::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
            ExprKind::Match { scrutinee, arms } => {
                let input = *children.first().ok_or("全域matchの実scrutineeがない")?;
                if input.0 >= limit || graph.context_at(input.0) != self.current_context(graph) {
                    return Err("全域matchの実scrutineeが未出・別Context".into());
                }
                self.source_matches(graph, self.evaluation(graph, input)?.0, *scrutinee)?;
                self.recheck_evaluation(graph, input)?;
                let value = self
                    .evaluation(graph, input)?
                    .2
                    .map(|r| graph.scalar(r))
                    .transpose()?;
                let selected = data::select(law, id, value, &self.control)?;
                std::iter::once(*scrutinee)
                    .chain(selected.map(|arm| arms[arm].body))
                    .collect()
            }
            ExprKind::Let { value, body, .. } => vec![*value, *body],
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => vec![*cond, *then_branch, *else_branch],
            ExprKind::Quant {
                split: QuantSplit::Fixed { body, .. },
                ..
            } => vec![*body],
            ExprKind::Call { args, .. } if self.named_view(id)?.is_some() => {
                let declaration = self.named_view(id)?.ok_or("全域call元宣言がない")?;
                let Signature::View { body, .. } = &declaration.signature else {
                    return Err("全域call元署名が違う".into());
                };
                if children.len() != args.len() + 1 {
                    return Err("全域call子数が違う".into());
                }
                let body_ref = *children.last().ok_or("全域call bodyがない")?;
                let context = graph.context_at(body_ref.0);
                let frame = graph
                    .frames
                    .get(context.frame.ok_or("全域call frameがない")?)
                    .ok_or("全域call frameがない")?;
                if frame.caller != self.current_context(graph)
                    || frame.source != source
                    || frame.arguments != children[..args.len()]
                {
                    return Err("全域callの実producerが違う".into());
                }
                self.source_matches(graph, self.evaluation(graph, body_ref)?.0, *body)?;
                for (&child, &original) in children.iter().zip(args) {
                    self.source_matches(graph, self.evaluation(graph, child)?.0, original)?;
                }
                for &child in children {
                    self.tick()?;
                    if child.0 >= limit {
                        return Err("全域call子が未出".into());
                    }
                    self.recheck_evaluation(graph, child)?;
                }
                return Ok(());
            }
            ExprKind::Dotted(_) if data::expression(law, id, &self.control)?.is_some() => vec![],
            ExprKind::Dotted(parts) => {
                let first = parts.first().ok_or("全域Dottedが空")?;
                if parts.len() == 1 {
                    if let Some((argument, _)) =
                        self.pattern_argument(graph, first.span, &first.name, bindings)?
                    {
                        if children != [argument] {
                            return Err("全域patternの実scrutinee producerが違う".into());
                        }
                    } else if let Some(argument) = self.call_parameter(graph, &first.name)? {
                        if children != [argument] {
                            return Err("全域名のcall producerが違う".into());
                        }
                    } else if let Some(argument) =
                        self.lexical_argument(graph, span, &first.name, bindings)?
                    {
                        if children != [argument] {
                            return Err("全域let producerがない".into());
                        }
                    } else if !children.is_empty() {
                        return Err("全域parameterに架空の観測producerがある".into());
                    }
                } else if parts.len() == 2 {
                    if children.len() != 1
                        || self.expression_span(graph, self.evaluation(graph, children[0])?.0)?
                            != first.span
                    {
                        return Err("全域fieldの実owner出現が違う".into());
                    }
                } else {
                    return Err("全域Dottedの長さが違う".into());
                }
                for &child in children {
                    self.tick()?;
                    if child.0 >= limit {
                        return Err("全域名のproducerが未出".into());
                    }
                    self.recheck_evaluation(graph, child)?;
                }
                return Ok(());
            }
            _ => self
                .composite_children(id)?
                .ok_or("全域式の元子構成がない")?,
        };
        if ids.len() != children.len() {
            return Err("全域評価の元AST子数が違う".into());
        }
        for (&child, &original) in children.iter().zip(&ids) {
            self.tick()?;
            if child.0 >= limit || graph.context_at(child.0) != self.current_context(graph) {
                return Err("全域評価の実子producer・Contextが違う".into());
            }
            let (expression, actual, _) = self.evaluation(graph, child)?;
            self.source_matches(graph, expression, original)?;
            if actual != bindings {
                return Err("全域評価の実子束縛が違う".into());
            }
            self.recheck_evaluation(graph, child)?;
        }
        Ok(())
    }

    pub(in crate::observed) fn universal_owned_evaluation(
        &self,
        graph: &Graph,
        reference: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::Evaluation { expression, .. }) = &graph.get(reference)?.payload else {
            return Ok(false);
        };
        Ok(self.universal_source_root(graph, *expression)?.is_some())
    }

    /// 数値全域parameterを持つ実field Sourceを、元Planで再分析する。
    /// 有限族のwhole Sourceや単なるScope継承をfield読取りへ昇格させない。
    pub(in crate::observed) fn universal_missing_source_analysis(
        &self,
        graph: &Graph,
        source: NodeRef,
    ) -> Result<Option<SourceAnalysis>, ValidationFailure> {
        self.validation_graph_session(graph, || {
            let previous = self.context.replace(Some(graph.context_at(source.0)));
            let previous_cutoff = self.cutoff.replace(source.0);
            let previous_universal = self.universal_context.replace(None);
            let result = self.universal_missing_source_analysis_in_context(graph, source);
            self.universal_context.replace(previous_universal);
            self.cutoff.set(previous_cutoff);
            self.context.set(previous);
            result
        })
    }

    fn universal_missing_source_analysis_in_context(
        &self,
        graph: &Graph,
        source: NodeRef,
    ) -> Result<Option<SourceAnalysis>, ValidationFailure> {
        self.tick()?;
        let node = graph.get(source)?;
        let Some(Payload::Expression {
            location: Location::Law { span },
            parameters,
            bindings,
        }) = &node.payload
        else {
            return Ok(None);
        };
        if parameters.is_empty() {
            return Ok(None);
        }
        for (_, ty) in parameters {
            self.tick()?;
            if !matches!(ty, Type::Z | Type::Q) {
                return Ok(None);
            }
        }
        let Some(&id) = self.expressions.get(span) else {
            return Ok(None);
        };
        if !matches!(&self.inputs.law().exprs[id].kind, ExprKind::Field { .. })
            && !matches!(&self.inputs.law().exprs[id].kind,ExprKind::Dotted(parts) if parts.len()>1)
        {
            return Ok(None);
        }
        let Some(&template) = node.arguments.first() else {
            return Ok(None);
        };
        if !self.universal_is_template(graph, template)? {
            return Ok(None);
        }
        let (_, fixed) = self.universal_source_fields(graph, template)?;
        let plan = self.universal_plan_at(graph, template, fixed)?;
        let domains = self.universal_domains_from(graph, node, template, &plan)?;
        let expected = std::iter::once(template)
            .chain(domains.iter().copied())
            .chain(self.source_arguments(graph, *span, bindings)?)
            .collect::<Vec<_>>();
        if node.arguments != expected {
            return Err("全域missing Sourceの元template・全型Domain・実binding辺が違う".into());
        }
        self.validate_at(graph, node, source.0)?;
        let analyzed =
            self.universal_source_analysis(graph, *span, bindings, &plan, &domains, template)?;
        if parameters != &analyzed.parameters
            || node.scope != analyzed.analysis.scope
            || node.ty
                != NodeType::Expression(
                    self.inputs
                        .law()
                        .expr_type(id)
                        .cloned()
                        .ok_or("全域missing Sourceの元field型がない")?,
                )
        {
            return Err("全域missing Sourceの元自由parameter・Scope・field型が違う".into());
        }
        Ok(analyzed
            .analysis
            .missing
            .is_some()
            .then_some(analyzed.analysis))
    }

    /// 同じ元AST出現を持つwholeの内部で、その全ASTを保持するroot評価。
    /// 通常のAST検索にはwholeを返し、この内部評価は検査してから除く。
    pub(in crate::observed) fn universal_internal_root_evaluation(
        &self,
        graph: &Graph,
        reference: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        self.validation_graph_session(graph, || {
            let previous = self.context.replace(Some(graph.context_at(reference.0)));
            let result = self.universal_internal_root_evaluation_in_context(graph, reference);
            self.context.set(previous);
            result
        })
    }

    fn universal_internal_root_evaluation_in_context(
        &self,
        graph: &Graph,
        reference: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        self.tick()?;
        let node = graph.get(reference)?;
        let Some(Payload::Evaluation {
            expression,
            bindings,
            ..
        }) = &node.payload
        else {
            return Ok(false);
        };
        let source = graph.get(*expression)?;
        let Some(Payload::Expression {
            location: Location::Law { span },
            bindings: source_bindings,
            ..
        }) = &source.payload
        else {
            return Ok(false);
        };
        let Some(&template) = source.arguments.first() else {
            return Ok(false);
        };
        if template == *expression || !self.universal_is_template(graph, template)? {
            return Ok(false);
        }
        let (template_span, fixed) = self.universal_source_fields(graph, template)?;
        if *span != template_span {
            // letの実引数など、内部root以外のpointwise評価は検索に残す。
            return Ok(false);
        }
        let plan = self.universal_plan_at(graph, template, fixed)?;
        if *span != plan.template_span
            || bindings != source_bindings
            || bindings != fixed
            || graph.context_at(reference.0) != graph.context_at(expression.0)
            || graph.context_at(reference.0) != graph.context_at(template.0)
            || node.ty != NodeType::Evaluation(Type::Bool)
            || source.ty != NodeType::Expression(Type::Bool)
        {
            return Err("全域内部rootの元AST・型・束縛・実Contextが違う".into());
        }
        let domains = self.universal_domains_from(graph, source, template, &plan)?;
        let expected = std::iter::once(template)
            .chain(domains.iter().copied())
            .chain(self.source_arguments(graph, *span, bindings)?)
            .collect::<Vec<_>>();
        if source.arguments != expected {
            return Err("全域内部rootの元template・全型Domain・AST辺が違う".into());
        }
        self.validate_at(graph, source, expression.0)?;
        self.validate_at(graph, node, reference.0)?;
        Ok(true)
    }
}
