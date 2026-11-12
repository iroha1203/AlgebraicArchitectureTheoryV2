//! 通常式の元出現と実子からの局所構成。内部生成とraw再検査で共有する。
use super::*;

pub(in crate::observed) struct Plan {
    span: (usize, usize),
    binder: bool,
    pub value: Option<Scalar>,
    pub reused: Option<NodeRef>,
    pub scope: Scope,
    pub scalar_scope: Scope,
    pub support: Support,
    pub reasons: Vec<Reason>,
    pub comparison: Option<(NodeRef, NodeRef)>,
    pub legacy: bool,
}

impl Environment<'_> {
    pub(in crate::observed) fn ordinary_children(
        &self,
        graph: &Graph,
        id: usize,
    ) -> Result<Option<Vec<usize>>, ValidationFailure> {
        if !self.ordinary_context(graph)? {
            return Ok(None);
        }
        Ok(match &self.indexes.inputs.law().exprs()[id].kind {
            ExprKind::Int(_) | ExprKind::Bool(_) => Some(vec![]),
            ExprKind::Group(child) => Some(vec![*child]),
            ExprKind::Let { value, body, .. } => Some(vec![*value, *body]),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => Some(vec![*cond, *then_branch, *else_branch]),
            ExprKind::Unary {
                op: UnOp::Not,
                operand,
            } => Some(vec![*operand]),
            ExprKind::Binary { op, lhs, rhs } if is_boolean_binary(*op) => Some(vec![*lhs, *rhs]),
            ExprKind::Binary {
                op: op @ (BinOp::Eq | BinOp::Ne),
                lhs,
                rhs,
            } if self.ordinary_comparison_type(*lhs, *op)? => Some(vec![*lhs, *rhs]),
            ExprKind::Call { callee, args }
                if args.len() == 1
                    && matches!(
                        self.indexes.inputs.law().expr_type(*callee),
                        Some(Type::Map(..))
                    ) =>
            {
                Some(vec![*callee, args[0]])
            }
            _ => None,
        })
    }

    fn ordinary_comparison_type(&self, lhs: usize, op: BinOp) -> Result<bool, ValidationFailure> {
        let law = self.indexes.inputs.law();
        let ty = law.expr_type(lhs).ok_or(internal!("比較の元型無し"))?;
        // Numeric residuals and extensional Term/Path certificates retain their dedicated path.
        // Data payloads cannot contain Path values (data::check_shape).
        Ok(!numeric::is_numeric_type(ty, &self.control)?
            && !super::super::term::contains(ty, law, &self.control)?
            && !super::super::path_value::contains_path(ty, &self.control)?
            && supports_binary(op, ty, law, &self.control)?)
    }

    /// Finite/object rows obtain bindings from their ObjectContext as well as
    /// explicit selectors; their dedicated raw Answer validator owns that contract.
    pub(in crate::observed) fn ordinary_answer_context(&self) -> bool {
        self.indexes.object.is_none()
            && self.indexes.object_instance.is_none()
            && self.indexes.object_values.is_none()
    }

    pub(in crate::observed) fn ordinary_context(
        &self,
        graph: &Graph,
    ) -> Result<bool, ValidationFailure> {
        let context = self.current_context(graph);
        if context.instance.is_some() || self.state.universal_context.borrow().is_some() {
            return Ok(false);
        }
        let mut current = context.iteration;
        while let Some(index) = current {
            let Some(record) = graph.iterations.get(index) else {
                return Ok(false);
            };
            if record
                .caller
                .iteration
                .is_some_and(|parent| parent >= index)
                || record.finite.is_none()
            {
                return Ok(false);
            }
            let Ok(span) = self.expression_span(graph, record.source) else {
                return Ok(false);
            };
            let Some(&id) = self.indexes.inputs.law().program().expressions.get(&span) else {
                return Ok(false);
            };
            if !self.ordinary_in_domain(id)? {
                return Ok(false);
            }
            current = record.caller.iteration;
        }
        Ok(true)
    }

    // The normalized producer is a real Set value. Nonprimitive collection
    // elements retain the original per-member Domain construction until that
    // container has an independently checked graph/wire representation.
    pub(in crate::observed) fn ordinary_in_domain(
        &self,
        id: usize,
    ) -> Result<bool, ValidationFailure> {
        let law = self.indexes.inputs.law();
        let ExprKind::Quant {
            split:
                archsig_input::law::ast::QuantSplit::Fixed {
                    domain: archsig_input::law::ast::QuantDomain::In(domain),
                    ..
                },
            ..
        } = &law.exprs()[id].kind
        else {
            return Ok(false);
        };
        let Some(Type::List(element) | Type::Set(element)) = law.expr_type(*domain) else {
            return Ok(false);
        };
        data::primitive_type(element, &self.control)
    }

    pub(in crate::observed) fn ordinary_source_eligible(
        &self,
        graph: &Graph,
        id: usize,
    ) -> Result<bool, ValidationFailure> {
        Ok(self.ordinary_context(graph)?
            && (self.ordinary_in_domain(id)? || self.ordinary_children(graph, id)?.is_some()))
    }

    /// 元AST/prefixの型付き出現のみを認証する。実行許可・値・欠測は生成しない。
    pub(in crate::observed) fn ordinary_source_at(
        &self,
        graph: &Graph,
        span: (usize, usize),
        ty: &Type,
        bindings: &[Binding],
    ) -> Result<Node, ValidationFailure> {
        if !self.ordinary_context(graph)? {
            return Err(internal!("静的Sourceの未対応Context").into());
        }
        let law = self.indexes.inputs.law();
        let actual = if let Some(&id) = law.program().expressions.get(&span) {
            law.expr_type(id)
                .ok_or(internal!("静的Sourceの元型無し"))?
                .clone()
        } else if let Some((id, count)) = self.dotted_prefix(span)? {
            let prefixes = self.dotted_prefixes(id)?;
            let (actual_span, ty) = prefixes
                .get(count - 1)
                .ok_or(internal!("元prefix範囲無し"))?;
            if *actual_span != span {
                return Err(internal!("元prefix span不一致").into());
            }
            ty.clone()
        } else {
            return Err(internal!("静的Sourceの型付き元出現無し").into());
        };
        if actual != *ty {
            return Err(internal!("静的Sourceの元型不一致").into());
        }
        let (scope, arguments) = self.validation_graph_session(graph, || {
            let context = self.current_context(graph);
            let previous = self.state.scoped_context.scoped(Some(context));
            let completion = self.state.completion_values.scoped(Vec::new());
            let result = (|| {
                if let Some(case) = context.case {
                    *self.state.completion_values.borrow_mut() =
                        self.completion_values(graph, case)?;
                }
                let mut scope = self
                    .analyze_source_with_guard(graph, span, bindings, None, true)?
                    .scope;
                let mut arguments = self.source_arguments_mode(graph, span, bindings, false)?;
                let mut chain = Vec::new();
                let mut current = context.iteration;
                while let Some(index) = current {
                    self.tick()?;
                    let record = graph
                        .iterations
                        .get(index)
                        .ok_or(internal!("静的Sourceの反復無し"))?;
                    if record
                        .caller
                        .iteration
                        .is_some_and(|parent| parent >= index)
                    {
                        return Err(internal!("静的Sourceの反復親が先行しない").into());
                    }
                    chain.push(index);
                    current = record.caller.iteration;
                }
                for index in chain.into_iter().rev() {
                    let (input, member, iteration_scope) = self.ordinary_iteration_input(
                        graph,
                        index,
                        graph.nodes.len().min(self.state.cutoff.get()),
                    )?;
                    let record = &graph.iterations[index];
                    if record.caller.request != context.request
                        || record.caller.frame != context.frame
                        || record.caller.instance != context.instance
                        || record.caller.case != context.case
                    {
                        return Err(internal!("静的Sourceの反復callerが違う").into());
                    }
                    let source_span = self.expression_span(graph, record.source)?;
                    let &id = law
                        .program()
                        .expressions
                        .get(&source_span)
                        .ok_or(internal!("反復元AST無し"))?;
                    let spec = quantifier::spec(law, id, &self.control)?;
                    let body = law.exprs()[spec.body].span;
                    if !(body.0 <= span.0 && span.1 <= body.1)
                        || self.expression_bindings(graph, record.source)? != bindings
                    {
                        return Err(internal!("静的Sourceが反復元body/束縛と違う").into());
                    }
                    scope.merge(&iteration_scope);
                    arguments.extend([
                        record.source,
                        input,
                        record.finite.ok_or(internal!("反復Domain無し"))?,
                        member,
                    ]);
                }
                Ok((scope, arguments))
            })();
            completion.restore();
            previous.restore();
            result
        })?;
        Ok(Node {
            ty: NodeType::Expression(ty.clone()),
            payload: Some(Payload::Expression {
                location: Location::Law { span },
                parameters: vec![],
                bindings: bindings.to_vec(),
            }),
            rule: Rule::OrdinarySource(Location::Law { span }),
            arguments,
            support: Support::default(),
            evidence: vec![],
            judgment: None,
            scope,
            reasons: vec![],
        })
    }

    pub(in crate::observed) fn ordinary_binder(
        &self,
        graph: &Graph,
        span: (usize, usize),
        limit: usize,
    ) -> Result<Option<(NodeRef, NodeRef, Scope)>, ValidationFailure> {
        if !self.ordinary_context(graph)? {
            return Ok(None);
        }
        let law = self.indexes.inputs.law();
        let (id, count) = if let Some(&id) = law.program().expressions.get(&span) {
            if !matches!(&law.exprs()[id].kind, ExprKind::Dotted(parts) if parts.len() == 1) {
                return Ok(None);
            }
            (id, 1)
        } else if let Some(prefix) = self.dotted_prefix(span)? {
            prefix
        } else {
            return Ok(None);
        };
        if count != 1 {
            return Ok(None);
        }
        let Some(lexical) = law.program().nodes[id].lexical.as_ref() else {
            return Ok(None);
        };
        if !matches!(
            lexical.source,
            archsig_input::law::ir::BindingSource::Iteration
        ) {
            return Ok(None);
        }
        let mut found = None;
        for (name, origin) in self.lexical_context(span)? {
            if name == lexical.name
                && let LexicalOrigin::Iteration(comp) = origin
            {
                if !self.ordinary_in_domain(comp)? {
                    return Ok(None);
                }
                let index = self
                    .iteration_for(graph, comp)?
                    .ok_or(internal!("In binderの実反復無し"))?;
                if found.replace(index).is_some() {
                    return Err(internal!("In binderの元出現が重複").into());
                }
            }
        }
        found
            .map(|index| self.ordinary_iteration_input(graph, index, limit))
            .transpose()
    }

    /// 実反復の位置/producerを照合する。元collection ASTを意味評価し直さない。
    pub(super) fn ordinary_iteration_input(
        &self,
        graph: &Graph,
        index: usize,
        limit: usize,
    ) -> Result<(NodeRef, NodeRef, Scope), ValidationFailure> {
        self.tick()?;
        let record = graph.iterations.get(index).ok_or(internal!("実反復無し"))?;
        let finite = record
            .finite
            .ok_or(internal!("In反復のfinite Domain無し"))?;
        let producer = record
            .producer
            .ok_or(internal!("In反復の実member producer無し"))?;
        if record
            .caller
            .iteration
            .is_some_and(|parent| parent >= index)
        {
            return Err(internal!("In反復親の先行性不正").into());
        }
        for reference in [record.source, record.domain, finite, producer] {
            if reference.0 >= limit || graph.context_at(reference.0) != record.caller {
                return Err(internal!("In反復refの先行性/Contextが違う").into());
            }
        }
        let law = self.indexes.inputs.law();
        let span = self.expression_span(graph, record.source)?;
        let &id = law
            .program()
            .expressions
            .get(&span)
            .ok_or(internal!("In反復元AST無し"))?;
        if !self.ordinary_in_domain(id)?
            || !matches!(graph.get(record.source)?.rule, Rule::OrdinarySource(_))
        {
            return Err(internal!("実In反復の元静的Sourceが違う").into());
        }
        let spec = quantifier::spec(law, id, &self.control)?;
        let Some(Payload::Evaluation {
            environment,
            expression,
            bindings,
            value: Some(value),
            ..
        }) = &graph.get(record.domain)?.payload
        else {
            return Err(internal!("未知/非評価collectionからIn反復がある").into());
        };
        if *environment != self.state.architecture_ref()
            || expression.0 >= record.domain.0
            || value.0 >= record.domain.0
            || self.expression_bindings(graph, record.source)? != bindings
        {
            return Err(internal!("In collectionの環境/束縛/先行性が違う").into());
        }
        self.source_matches(
            graph,
            *expression,
            spec.domain.ok_or(internal!("In collection元AST無し"))?,
        )?;
        if graph
            .get(record.domain)?
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
        {
            return Err(internal!("Failed collectionからIn反復がある").into());
        }
        let domain = graph.get(finite)?;
        let Some(Payload::Domain { ty, elements }) = &domain.payload else {
            return Err(internal!("In finite Domainのpayloadが違う").into());
        };
        if domain.arguments.get(..2) != Some([record.source, record.domain].as_slice())
            || elements.get(record.position) != Some(&producer)
            || *ty != spec.element
            || producer.0 >= finite.0
        {
            return Err(internal!("In Domainの元refs/実member位置/型が違う").into());
        }
        let super::super::call::Member::SetElement(member) = &record.member else {
            return Err(internal!("In実member identityが要素でない").into());
        };
        if graph.scalar(producer)? != member || graph.scalar(producer)?.ty() != spec.element {
            return Err(internal!("In実member producerの値/型が違う").into());
        }
        if !matches!(
            graph.scalar(*value)?,
            Scalar::List { .. } | Scalar::Set { .. }
        ) {
            return Err(internal!("In collectionがList/Setでない").into());
        }
        let mut scope = domain.scope.clone();
        scope.add_quantifier(spec.descriptor(Some(finite), Some(record.caller)));
        self.order_quantifier_scope(graph, record.source, &mut scope)?;
        Ok((record.domain, producer, scope))
    }

    pub(in crate::observed) fn ordinary_plan(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<Plan, ValidationFailure> {
        if source.0 >= limit {
            return Err(internal!("通常式Sourceが未出").into());
        }
        if !matches!(graph.get(source)?.rule, Rule::OrdinarySource(_)) {
            return Err(internal!("通常構成のSource規則が違う").into());
        }
        let span = self.expression_span(graph, source)?;
        let bindings = self.expression_bindings(graph, source)?;
        let law = self.indexes.inputs.law();
        if let Some((input, producer, _)) = self.ordinary_binder(graph, span, limit)? {
            if children != [input] || graph.context_at(source.0) != self.current_context(graph) {
                return Err(internal!("In binderの実collection子/Contextが違う").into());
            }
            let input_node = graph.get(input)?;
            let mut scope = graph.get(source)?.scope.clone();
            scope.merge(&input_node.scope);
            return Ok(Plan {
                span,
                binder: true,
                comparison: None,
                legacy: false,
                value: Some(graph.scalar(producer)?.clone()),
                reused: None,
                scalar_scope: scope.clone(),
                scope,
                support: input_node.support.clone(),
                reasons: input_node.reasons.clone(),
            });
        }
        let id = *law
            .program()
            .expressions
            .get(&span)
            .ok_or(internal!("通常式の元ASTがない"))?;
        let expected = self
            .ordinary_children(graph, id)?
            .ok_or(internal!("通常式の未対応AST"))?;
        if children.len() != expected.len()
            || graph.context_at(source.0) != self.current_context(graph)
        {
            return Err(internal!("通常式の子数/Contextが違う").into());
        }
        let mut scope = graph.get(source)?.scope.clone();
        let mut scalar_scope = scope.clone();
        let mut factors = Vec::new();
        let mut values = Vec::new();
        let mut pending = Vec::new();
        for (&child, id) in children.iter().zip(expected) {
            self.tick()?;
            if child.0 >= limit || graph.context_at(child.0) != self.current_context(graph) {
                return Err(internal!("実子Evaluationが未出/別Context").into());
            }
            let node = graph.get(child)?;
            let Some(Payload::Evaluation {
                environment,
                expression,
                bindings: actual,
                value,
                ..
            }) = &node.payload
            else {
                return Err(internal!("実子がEvaluationでない").into());
            };
            if *environment != self.state.architecture_ref()
                || actual != bindings
                || self.expression_span(graph, *expression)? != law.exprs()[id].span
                || node.ty
                    != NodeType::Evaluation(
                        law.expr_type(id)
                            .ok_or(internal!("子の元型がない"))?
                            .clone(),
                    )
                || expression.0 >= child.0
                || value.is_some_and(|value| value.0 >= child.0)
            {
                return Err(internal!("実子の元AST/型/束縛/環境/先行性が違う").into());
            }
            scope.merge(&node.scope);
            scalar_scope.merge(&node.scope);
            factors.push(node.support.clone());
            values.push(*value);
            pending.push(self.evaluation_condition_pending(graph, child)?);
        }
        let mut required = vec![true; children.len()];
        let scalar = |i: usize| values[i].map(|r| graph.scalar(r)).transpose();
        let mut reused = None;
        let mut comparison = None;
        let mut legacy = false;
        let known = match &law.exprs()[id].kind {
            ExprKind::Int(n) => Some(numeric::literal(
                n,
                law.expr_type(id).ok_or(internal!("literal型無し"))?,
                &self.control,
            )?),
            ExprKind::Bool(b) => Some(Scalar::Bool(*b)),
            ExprKind::Group(_) => {
                reused = values[0];
                scalar(0)?.cloned()
            }
            ExprKind::Let { .. } => scalar(1)?.cloned(),
            ExprKind::If { .. } => {
                match scalar(0)? {
                    Some(Scalar::Bool(true)) => required[2] = false,
                    Some(Scalar::Bool(false)) => required[1] = false,
                    _ => {}
                }
                conditional_branch(scalar(0)?, scalar(1)?, scalar(2)?, law, &self.control)?
            }
            ExprKind::Unary { op: UnOp::Not, .. } => scalar(0)?
                .map(|value| unary(UnOp::Not, value, &self.control))
                .transpose()?,
            ExprKind::Call { .. } => {
                if let Some((map, key)) = scalar(0)?.zip(scalar(1)?) {
                    let selected = data::map_apply(map, key, law, &self.control)?;
                    legacy = selected.is_none();
                    selected
                } else {
                    legacy = true;
                    None
                }
            }
            ExprKind::Binary { op, .. } => {
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    comparison = values[0].zip(values[1]);
                    legacy = comparison.is_none();
                }
                if is_boolean_binary(*op)
                    && matches!(
                        (op, scalar(0)?),
                        (BinOp::And | BinOp::Implies, Some(Scalar::Bool(false)))
                            | (BinOp::Or, Some(Scalar::Bool(true)))
                    )
                {
                    required[1] = false;
                }
                partial_binary(*op, scalar(0)?, scalar(1)?, law, span, &self.control)?
            }
            _ => return Err(internal!("通常式の未対応規則").into()),
        };
        let mut reasons = self.evaluation_child_reasons(graph, source, children)?;
        sort_reasons(&mut reasons);
        let pending = pending
            .iter()
            .zip(&required)
            .any(|(pending, required)| *pending && *required);
        let failed = reasons
            .iter()
            .any(|reason| matches!(reason.kind, ReasonKind::ConditionFailed { .. }));
        let value = if pending || failed {
            reused = None;
            None
        } else {
            known
        };
        if let Some(reference) = reused {
            scalar_scope = graph.get(reference)?.scope.clone();
        }
        Ok(Plan {
            span,
            binder: false,
            comparison,
            legacy,
            value,
            reused,
            scope,
            scalar_scope,
            support: Support::sum(vec![], factors),
            reasons,
        })
    }

    /// Pendingの消費は値・Scope・支持の再構成を伴わない。
    pub(super) fn ordinary_pending(
        &self,
        graph: &Graph,
        evaluation: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::Evaluation {
            expression,
            parts,
            value,
            ..
        }) = &graph.get(evaluation)?.payload
        else {
            return Err(internal!("通常PendingのEvaluationがない").into());
        };
        if value.is_some() {
            return Ok(false);
        }
        let children = &parts
            .first()
            .ok_or(internal!("通常Pendingのpartがない"))?
            .children;
        let span = self.expression_span(graph, *expression)?;
        let id = *self
            .indexes
            .inputs
            .law()
            .program()
            .expressions
            .get(&span)
            .ok_or(internal!("通常PendingのASTがない"))?;
        let mut required = vec![true; children.len()];
        let boolean = |index: usize| {
            self.evaluation(graph, children[index])
                .and_then(|(_, _, value)| graph.boolean(value))
        };
        match &self.indexes.inputs.law().exprs()[id].kind {
            ExprKind::If { .. } if children.len() == 3 => match boolean(0)? {
                Some(true) => required[2] = false,
                Some(false) => required[1] = false,
                None => {}
            },
            ExprKind::Binary { op, .. } if children.len() == 2 && is_boolean_binary(*op) => {
                if matches!(
                    (op, boolean(0)?),
                    (BinOp::And | BinOp::Implies, Some(false)) | (BinOp::Or, Some(true))
                ) {
                    required[1] = false;
                }
            }
            _ => {}
        }
        for (child, required) in children.iter().zip(required) {
            if required && self.evaluation_condition_pending(graph, *child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(in crate::observed) fn ordinary_value_node(
        &self,
        source: NodeRef,
        children: &[NodeRef],
        plan: &Plan,
    ) -> Option<Node> {
        if plan.legacy || plan.reused.is_some() {
            return None;
        }
        plan.value.as_ref().map(|value| Node {
            ty: NodeType::Value(value.ty()),
            payload: Some(Payload::Scalar(value.clone())),
            rule: if plan.binder {
                Rule::BinderValue(Location::Law { span: plan.span })
            } else if plan.comparison.is_some()
                || self
                    .indexes
                    .inputs
                    .law()
                    .program()
                    .expressions
                    .get(&plan.span)
                    .is_some_and(|id| {
                        matches!(
                            self.indexes.inputs.law().exprs()[*id].kind,
                            ExprKind::Call { .. }
                        )
                    })
            {
                Rule::OperandValue(Location::Law { span: plan.span })
            } else {
                Rule::OrdinaryValue(Location::Law { span: plan.span })
            },
            arguments: std::iter::once(source)
                .chain(children.iter().copied())
                .collect(),
            support: plan.support.clone(),
            scope: plan.scalar_scope.clone(),
            evidence: vec![],
            judgment: None,
            reasons: vec![],
        })
    }

    pub(in crate::observed) fn ordinary_evaluation_node(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        value: Option<NodeRef>,
        plan: &Plan,
    ) -> Result<Node, ValidationFailure> {
        if plan.legacy {
            return Err(internal!("既存意味計算が必要な式を通常局所結果にできない").into());
        }
        let NodeType::Expression(ty) = &graph.get(source)?.ty else {
            return Err(internal!("通常式Source型無し").into());
        };
        let span = self.expression_span(graph, source)?;
        Ok(Node {
            ty: NodeType::Evaluation(ty.clone()),
            payload: Some(Payload::Evaluation {
                environment: self.state.architecture_ref(),
                expression: source,
                bindings: self.expression_bindings(graph, source)?.to_vec(),
                parts: vec![Part {
                    location: Location::Law { span },
                    value,
                    residual: None,
                    children: children.to_vec(),
                }],
                value,
                applicability: "applicable",
            }),
            rule: Rule::Construction("ordinary_evaluation"),
            arguments: std::iter::once(source)
                .chain(children.iter().copied())
                .chain(value)
                .collect(),
            support: plan.support.clone(),
            scope: plan.scope.clone(),
            reasons: plan.reasons.clone(),
            evidence: value
                .map(|r| graph.get(r).map(|n| n.evidence.clone()))
                .transpose()?
                .unwrap_or_default(),
            judgment: None,
        })
    }

    pub(super) fn validate_ordinary(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let rule = match &node.rule {
            Rule::OrdinarySource(_) => "ordinary_source",
            Rule::OrdinaryValue(_) | Rule::BinderValue(_) | Rule::OperandValue(_) => {
                "ordinary_value"
            }
            Rule::Construction("ordinary_evaluation") => "ordinary_evaluation",
            _ => return Ok(false),
        };
        self.validate_node_inputs(graph, node, limit)?;
        for reference in &node.arguments {
            if reference.0 >= limit {
                return Err(internal!("通常構成の依存が未出").into());
            }
            self.validate_at(graph, graph.get(*reference)?, reference.0)?;
        }
        let expected = if rule == "ordinary_source" {
            let Some(Payload::Expression {
                location: Location::Law { span },
                bindings,
                ..
            }) = &node.payload
            else {
                return Err(internal!("通常Sourceのpayload不正").into());
            };
            let NodeType::Expression(ty) = &node.ty else {
                return Err(internal!("静的Source型無し").into());
            };
            self.ordinary_source_at(graph, *span, ty, bindings)?
        } else {
            let source = *node
                .arguments
                .first()
                .ok_or(internal!("通常構成のSource無し"))?;
            if rule == "ordinary_value" {
                let children = &node.arguments[1..];
                let plan = self.ordinary_plan(graph, source, children, limit)?;
                self.ordinary_value_node(source, children, &plan)
                    .ok_or(internal!("通常値が生成対象でない"))?
            } else {
                let Some(Payload::Evaluation { parts, value, .. }) = &node.payload else {
                    return Err(internal!("通常Evaluationのpayload不正").into());
                };
                if parts.len() != 1 {
                    return Err(internal!("通常Evaluationのpart数不正").into());
                }
                let children = &parts[0].children;
                let plan = self.ordinary_plan(graph, source, children, limit)?;
                if plan.reused.is_some() {
                    if *value != plan.reused {
                        return Err(internal!("通常aliasの値refが違う").into());
                    }
                } else if let Some(expected) = self.ordinary_value_node(source, children, &plan) {
                    let value = value.ok_or(internal!("通常式の値無し"))?;
                    if !graph
                        .get(value)?
                        .matches_with_support(&expected, &self.control)?
                    {
                        return Err(internal!("通常Scalarが元規則と違う").into());
                    }
                } else if value.is_some() {
                    return Err(internal!("未確定通常式に値がある").into());
                }
                self.ordinary_evaluation_node(graph, source, children, *value, &plan)?
            }
        };
        if !node.matches_with_support(&expected, &self.control)? {
            return Err(internal!("通常構成が元AST/実子の局所規則と違う").into());
        }
        Ok(true)
    }
}

#[cfg(test)]
impl Environment<'_> {
    /// テストが通常実行とcold検査で同じcollectorを観測するための状態交換。
    pub(in crate::observed) fn ordinary_test_read_collectors(
        &self,
        primitive: Option<BTreeSet<Fact>>,
        missing: Option<BTreeSet<Fact>>,
    ) -> (Option<BTreeSet<Fact>>, Option<BTreeSet<Fact>>) {
        (
            self.state.primitive_reads.replace(primitive),
            self.state.missing_slot_reads.replace(missing),
        )
    }
}

// In collection's one-shot normalization and positional coverage share the
// ordinary private construction / independent raw-validation boundary.
mod domain;
pub(in crate::observed) use domain::InDomain;
