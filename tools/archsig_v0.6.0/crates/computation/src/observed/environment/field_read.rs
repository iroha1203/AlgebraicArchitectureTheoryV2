//! 実field取得の効果境界と、記述からの局所値照合。
use super::*;

pub(in crate::observed) struct FieldPlan {
    pub span: (usize, usize),
    pub source: NodeRef,
    pub origin: NodeRef,
    pub position: Option<Fact>,
    pub child: NodeRef,
    pub ty: Type,
    pub value: Option<std::sync::Arc<Scalar>>,
    pub reused: Option<NodeRef>,
    pub assigned: Option<NodeRef>,
    pub scope: Scope,
    pub scalar_scope: Scope,
    pub support: Support,
    pub scalar_support: Support,
    pub scalar_rule: Option<Rule>,
    pub reasons: Vec<Reason>,
}

/// Already selected receiver data. The plan carries the source Scope and the
/// actual child's Support/reasons; these borrowed inputs need no Graph lookup.
pub(in crate::observed) struct FieldReceiver<'a> {
    pub value: Option<&'a Scalar>,
    pub pending: bool,
    pub scope: &'a Scope,
    pub request: Option<&'a Request>,
}

impl<'a> Environment<'a> {
    pub(super) fn field_read_collecting(&self) -> bool {
        self.state.primitive_reads.borrow().is_some()
            || self.state.missing_slot_reads.borrow().is_some()
    }

    fn field_spec(
        &self,
        span: (usize, usize),
    ) -> Result<(archsig_common::names::QualifiedName, (usize, usize), Type), ValidationFailure>
    {
        let law = self.indexes.inputs.law();
        if let Some(&id) = law.program().expressions.get(&span) {
            let expression = &law.program().nodes[id];
            if let ExprKind::Field { base, .. } = expression.kind {
                return Ok((
                    expression
                        .field
                        .as_ref()
                        .ok_or(internal!("fieldの静的解決がない"))?
                        .clone(),
                    law.exprs()[base].span,
                    law.expr_type(id)
                        .ok_or(internal!("fieldの元型がない"))?
                        .erase(),
                ));
            }
        }
        let (id, count) = self
            .dotted_prefix(span)?
            .ok_or(internal!("fieldの元prefixがない"))?;
        if count < 2 {
            return Err(internal!("fieldが先頭binderを指す").into());
        }
        let prefixes = self.dotted_prefixes(id)?;
        let lexical = law.program().nodes[id]
            .lexical
            .as_ref()
            .ok_or(internal!("fieldの元lexical解決がない"))?;
        let projection = lexical
            .projections
            .get(count - 2)
            .ok_or(internal!("fieldの元projectionがない"))?;
        let previous = prefixes
            .get(count - 2)
            .ok_or(internal!("fieldの直前prefixがない"))?;
        Ok((projection.name.clone(), previous.0, projection.ty.erase()))
    }

    /// pureなdescriptor取得の外側にある実read境界。cold再検査も現collectorへ公開する。
    pub(in crate::observed) fn field_read_observation(
        &self,
        graph: &Graph,
        source: NodeRef,
        child: NodeRef,
        limit: usize,
        retained: impl FnOnce(&Scope, &[Reason]),
    ) -> Result<FieldPlan, ValidationFailure> {
        if source.0 >= limit
            || child.0 >= limit
            || graph.context_at(source.0) != self.current_context(graph)
            || graph.context_at(child.0) != self.current_context(graph)
            || !matches!(graph.get(source)?.rule, Rule::OrdinarySource(_))
        {
            return Err(internal!("fieldの実Source/子の先行性・Contextが違う").into());
        }
        let span = self.expression_span(graph, source)?;
        let (name, base_span, ty) = self.field_spec(span)?;
        graph.expect(source, &NodeType::Expression(ty.clone()))?;
        let node = graph.get(child)?;
        let Some(Payload::Evaluation {
            expression,
            bindings,
            value,
            environment,
            ..
        }) = &node.payload
        else {
            return Err(internal!("fieldの実baseがEvaluationでない").into());
        };
        if self.expression_span(graph, *expression)? != base_span
            || bindings != self.expression_bindings(graph, source)?
            || *environment != self.state.architecture_ref()
            || expression.0 >= child.0
            || value.is_some_and(|r| r.0 >= child.0)
        {
            return Err(internal!("fieldの実baseの元出現・束縛・環境が違う").into());
        }
        let scope = graph.get(source)?.scope.clone();
        let reasons = self.evaluation_child_reasons(graph, source, &[child])?;
        let plan = FieldPlan {
            span,
            source,
            origin: source,
            position: None,
            child,
            ty,
            value: None,
            reused: None,
            assigned: None,
            scalar_scope: graph.get(source)?.scope.clone(),
            scope,
            support: node.support.clone(),
            scalar_support: Support::default(),
            scalar_rule: None,
            reasons,
        };
        // The Graph adapter authenticates the actual receiver once. The shared
        // read boundary below consumes its value and condition state directly.
        let pending = if value.is_none() {
            self.evaluation_condition_pending(graph, child)?
        } else {
            false
        };
        let receiver = value.map(|reference| graph.scalar(reference)).transpose()?;
        self.observe_field_receiver(
            plan,
            &name,
            FieldReceiver {
                value: receiver,
                pending,
                scope: &node.scope,
                request: graph.requests.get(self.current_context(graph).request),
            },
            retained,
        )
    }

    /// Shared actual-read boundary. Source/child authentication and recording
    /// remain in the Graph adapter; no receiver value is re-extracted here.
    pub(in crate::observed) fn observe_field_receiver(
        &self,
        mut plan: FieldPlan,
        name: &archsig_common::names::QualifiedName,
        receiver: FieldReceiver<'_>,
        retained: impl FnOnce(&Scope, &[Reason]),
    ) -> Result<FieldPlan, ValidationFailure> {
        let span = plan.span;
        plan.scope.merge(receiver.scope);
        let Some(value) = receiver.value else {
            if receiver.pending
                || plan
                    .reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            {
                retained(&plan.scope, &[]);
                return Ok(plan);
            }
            return Err(ValidationFailure::UnsupportedExpression {
                location: Location::Law { span },
                feature: "未確定の参照からの field 読取り".into(),
            });
        };
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = value
        else {
            return Err(internal!("fieldの実baseが原始Refでない").into());
        };
        let owner = self.indexes.subject(snapshot, subject)?;
        if owner.ty != *entity || name.owner() != Some(entity.as_str()) {
            return Err(internal!("fieldの実owner型が違う").into());
        }
        let field = self.indexes.field_descriptor(snapshot, subject, name)?;
        if field.ty.erase() != plan.ty {
            return Err(internal!("fieldの元slot型が違う").into());
        }
        self.indexes
            .record_field_read(&self.state, snapshot, subject, field);
        let position = Fact::from(archsig_input::archmap::FactData {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field: Some(field.name.clone()),
            atom: None,
        });
        let architecture = self.state.architecture_value_reference(&position);
        let origin = if architecture.is_some() {
            None
        } else {
            match &field.slot {
                Slot::Known { origin, .. } => Some(origin.as_str()),
                Slot::Missing => None,
            }
        };
        let reading = self
            .indexes
            .inputs
            .law()
            .declarations()
            .values()
            .find(|d| d.span.0 <= span.0 && span.1 <= d.span.1)
            .ok_or(internal!("fieldの元宣言がない"))?
            .reading
            .as_str();
        let read_scope = self.indexes.scope(owner, reading, origin)?;
        plan.scope.merge(&read_scope);
        plan.scalar_scope.merge(&read_scope);
        // 値自身のleaf範囲へ、実binderの量化座標だけを継ぐ。
        plan.scalar_scope.merge_quantifiers(receiver.scope);
        if architecture.is_some() {
            self.state.merge_architecture_scope(&mut plan.scope);
        } else if matches!(field.slot, Slot::Missing) {
            plan.scope.completions = true;
            plan.scalar_scope.completions = true;
            let request = receiver
                .request
                .ok_or(internal!("fieldの元Requestがない"))?;
            plan.reasons.push(Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: vec![plan.origin],
                missing: vec![position.clone()],
                location: Some(Location::Law { span }),
            });
        }
        plan.position = Some(position);
        // read Scopeはcarrier挿入前の停止でも残す。canonical理由はcarrierのcommit時に公開する。
        retained(&plan.scope, &[]);
        Ok(plan)
    }

    pub(in crate::observed) fn field_read_source_node(
        &self,
        graph: &Graph,
        plan: &FieldPlan,
    ) -> Result<Node, ValidationFailure> {
        if plan.position.is_none() {
            return Err(internal!("未実行fieldにread Sourceを作った").into());
        }
        Ok(Node {
            ty: NodeType::Expression(plan.ty.clone()),
            payload: graph.get(plan.origin)?.payload.clone(),
            rule: Rule::FieldSource(Location::Law { span: plan.span }),
            arguments: vec![plan.origin, plan.child],
            scope: plan.scope.clone(),
            support: Support::default(),
            reasons: vec![],
            evidence: vec![],
            judgment: None,
        })
    }

    pub(in crate::observed) fn field_bind_read_source(
        &self,
        plan: &mut FieldPlan,
        source: NodeRef,
    ) {
        for reason in &mut plan.reasons {
            if reason.kind == ReasonKind::Missing
                && reason.dependencies == [plan.origin]
                && reason.location == Some(Location::Law { span: plan.span })
            {
                reason.dependencies = vec![source];
            }
        }
        plan.source = source;
    }

    pub(in crate::observed) fn resolve_field_read(
        &self,
        graph: &Graph,
        plan: &mut FieldPlan,
    ) -> Result<(), ValidationFailure> {
        let Some(position) = plan.position.clone() else {
            return Ok(());
        };
        let field = self.indexes.field_descriptor(
            &position.snapshot,
            &position.subject,
            position
                .field
                .as_deref()
                .ok_or(internal!("fieldの原始位置名がない"))?,
        )?;
        let architecture = self.state.architecture_value_reference(&position);
        self.resolve_field_descriptor(graph, field, &position, architecture, plan)
    }

    /// descriptorを再取得せず、collectorを変更せずに元解決順を計算する。
    fn resolve_field_descriptor(
        &self,
        graph: &Graph,
        field: &'a archsig_input::archmap::Field,
        position: &Fact,
        architecture: Option<NodeRef>,
        plan: &mut FieldPlan,
    ) -> Result<(), ValidationFailure> {
        if !matches!(field.ty, Type::Bool | Type::Ref(_) | Type::Owned(_, _))
            && !data::supported(&field.ty.erase(), self.indexes.inputs.law(), &self.control)?
        {
            return Err(ValidationFailure::UnsupportedExpression {
                location: Location::Law { span: plan.span },
                feature: "Z/Bool/Ref 以外の原始 slot 評価".into(),
            });
        }
        if let Some(reference) = architecture {
            plan.reused = Some(reference);
            plan.support = Support::sum(
                vec![],
                [plan.support.clone(), graph.get(reference)?.support.clone()],
            );
            return Ok(());
        }
        let chain = self.dotted_prefix(plan.span)?.is_some_and(|(id, count)| {
            count > 1 && matches!(&self.indexes.inputs.law().exprs()[id].kind, ExprKind::Dotted(parts) if parts.len()>2)
        });
        let resolved =
            if let Some((value, fact)) = self.object_field_value_descriptor(position, field)? {
                plan.scalar_rule = Some(if chain {
                    Rule::FieldValue {
                        kind: "law",
                        location: Some(Location::Law { span: plan.span }),
                    }
                } else {
                    Rule::FieldValue {
                        kind: "object_field",
                        location: None,
                    }
                });
                Some((std::sync::Arc::new(value), Some(fact)))
            } else if self.completion_type_supported(&field.ty)?
                && matches!(field.slot, Slot::Missing)
                && let Some(assigned) = self.completion_slot(graph, position)?
            {
                plan.assigned = Some(assigned);
                plan.scalar_rule = Some(Rule::FieldValue {
                    kind: "law",
                    location: Some(Location::Law { span: plan.span }),
                });
                Some((
                    match &graph.get(assigned)?.payload {
                        Some(Payload::Scalar(value)) => value.clone(),
                        _ => std::sync::Arc::new(graph.scalar(assigned)?.clone()),
                    },
                    None,
                ))
            } else if let Slot::Known { atom, pointer, .. } = &field.slot {
                plan.scalar_rule = Some(Rule::FieldValue {
                    kind: if chain { "law" } else { "atom" },
                    location: Some(if chain {
                        Location::Law { span: plan.span }
                    } else {
                        Location::ArchMap {
                            pointer: pointer.clone(),
                            span: None,
                        }
                    }),
                });
                let value = self
                    .indexes
                    .observed_scalar(field, &self.control)?
                    .ok_or_else(|| ValidationFailure::UnsupportedExpression {
                        location: Location::Law { span: plan.span },
                        feature: "Z/Bool/Ref 以外の原始値読取り".into(),
                    })?;
                let mut fact = position.clone();
                fact.atom = Some(atom.clone());
                Some((std::sync::Arc::new(value), Some(fact)))
            } else {
                None
            };
        if let Some((value, fact)) = resolved {
            plan.value = Some(value);
            let mut own = Vec::new();
            if let Some(fact) = fact {
                plan.scalar_support = vec![fact.clone()].into();
                own.push(fact);
            }
            plan.support = Support::sum(own, [plan.support.clone()]);
        }
        sort_reasons(&mut plan.reasons);
        Ok(())
    }

    pub(in crate::observed) fn field_value_node(&self, plan: &FieldPlan) -> Option<Node> {
        let value = plan.value.as_ref()?;
        Some(Node {
            ty: NodeType::Value(plan.ty.clone()),
            payload: Some(Payload::scalar(value.clone())),
            rule: plan.scalar_rule.clone()?,
            arguments: vec![plan.source, plan.child]
                .into_iter()
                .chain(plan.assigned)
                .collect(),
            support: plan.scalar_support.clone(),
            scope: plan.scalar_scope.clone(),
            evidence: vec![],
            judgment: None,
            reasons: vec![],
        })
    }
    pub(in crate::observed) fn field_evaluation_node(
        &self,
        graph: &Graph,
        plan: &FieldPlan,
        value: Option<NodeRef>,
    ) -> Result<Node, ValidationFailure> {
        Ok(Node {
            ty: NodeType::Evaluation(plan.ty.clone()),
            payload: Some(Payload::Evaluation {
                environment: self.state.architecture_ref(),
                expression: plan.source,
                bindings: self.expression_bindings(graph, plan.source)?.to_vec(),
                parts: vec![Part {
                    location: Location::Law { span: plan.span },
                    value,
                    residual: None,
                    children: vec![plan.child],
                }],
                value,
                applicability: "applicable",
            }),
            rule: Rule::Construction("field_evaluation"),
            arguments: vec![plan.source, plan.child]
                .into_iter()
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

    /// 名前の値を計算し直さず、元binding/実引数/let RHSのproducerを再使用する。
    pub(in crate::observed) fn alias_evaluation_node(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        value: Option<NodeRef>,
        limit: usize,
    ) -> Result<Node, ValidationFailure> {
        if source.0 >= limit
            || graph.context_at(source.0) != self.current_context(graph)
            || !matches!(graph.get(source)?.rule, Rule::OrdinarySource(_))
        {
            return Err(internal!("aliasの元Sourceの先行性/Contextが違う").into());
        }
        let span = self.expression_span(graph, source)?;
        let bindings = self.expression_bindings(graph, source)?;
        // The optional test observer follows the real alias producer as well
        // as cold validation, at the same existing name-token checkpoint.
        #[cfg(test)]
        let previous_name_context = self
            .state
            .optional_name_context
            .scoped(Some(self.current_context(graph)));
        let name = self.name_token(span);
        #[cfg(test)]
        previous_name_context.restore();
        let name = name?;
        let expected = if let Some(rhs) = self.lexical_rhs(span, name)? {
            Some(self.actual_evaluation_reference(graph, rhs, bindings)?)
        } else {
            self.call_parameter(graph, name)?
        };
        let mut scope = graph.get(source)?.scope.clone();
        let (support, reasons) = if let Some(expected) = expected {
            if children != [expected]
                || expected.0 >= limit
                || self.evaluation(graph, expected)?.2 != value
            {
                return Err(internal!("aliasの元実producer/value refが違う").into());
            }
            let node = graph.get(expected)?;
            scope.merge(&node.scope);
            (node.support.clone(), node.reasons.clone())
        } else {
            if !children.is_empty() {
                return Err(internal!("parameterに別producer子がある").into());
            }
            self.check_parameter(graph, bindings, name, value)?;
            let reference = value.ok_or(internal!("parameterの既出値がない"))?;
            if reference.0 >= limit {
                return Err(internal!("parameterの値が未出").into());
            }
            scope.merge(&graph.get(reference)?.scope);
            (graph.get(reference)?.support.clone(), vec![])
        };
        let NodeType::Expression(ty) = &graph.get(source)?.ty else {
            return Err(internal!("aliasの元型がない").into());
        };
        if let Some(reference) = value {
            graph.expect(reference, &NodeType::Value(ty.clone()))?;
        }
        Ok(Node {
            ty: NodeType::Evaluation(ty.clone()),
            payload: Some(Payload::Evaluation {
                environment: self.state.architecture_ref(),
                expression: source,
                bindings: bindings.to_vec(),
                parts: vec![Part {
                    location: Location::Law { span },
                    value,
                    residual: None,
                    children: children.to_vec(),
                }],
                value,
                applicability: "applicable",
            }),
            rule: Rule::Construction("alias_evaluation"),
            arguments: std::iter::once(source)
                .chain(children.iter().copied())
                .chain(value)
                .collect(),
            support,
            scope,
            reasons,
            evidence: value
                .map(|r| graph.get(r).map(|node| node.evidence.clone()))
                .transpose()?
                .unwrap_or_default(),
            judgment: None,
        })
    }

    pub(super) fn validate_field_read(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if node.rule == Rule::Construction("alias_evaluation") {
            self.validate_node_inputs(graph, node, limit)?;
            for &reference in &node.arguments {
                if reference.0 >= limit {
                    return Err(internal!("aliasの依存が未出").into());
                }
                self.validate_at(graph, graph.get(reference)?, reference.0)?;
            }
            let Some(Payload::Evaluation {
                expression,
                parts,
                value,
                ..
            }) = &node.payload
            else {
                return Err(internal!("aliasのpayloadがない").into());
            };
            if parts.len() != 1 {
                return Err(internal!("aliasのpart数が違う").into());
            }
            let expected =
                self.alias_evaluation_node(graph, *expression, &parts[0].children, *value, limit)?;
            if !node.matches_with_support(&expected, &self.control)? {
                return Err(internal!("aliasの実入力/Scope/理由が元producerと違う").into());
            }
            return Ok(true);
        }
        if matches!(node.rule, Rule::FieldSource(_)) {
            self.validate_node_inputs(graph, node, limit)?;
            let [origin, child] = node.arguments.as_slice() else {
                return Err(internal!("field read Sourceの依存数が違う").into());
            };
            for &reference in &node.arguments {
                if reference.0 >= limit {
                    return Err(internal!("field read Sourceの依存が未出").into());
                }
                self.validate_at(graph, graph.get(reference)?, reference.0)?;
            }
            let plan = self.field_read_observation(graph, *origin, *child, limit, |_, _| {})?;
            let expected = self.field_read_source_node(graph, &plan)?;
            if !node.matches_with_support(&expected, &self.control)? {
                return Err(internal!("field read Sourceが元slot/実base/Scopeと違う").into());
            }
            return Ok(true);
        }
        let is_value = match node.rule {
            Rule::FieldValue { .. } => true,
            Rule::Construction("field_evaluation") => false,
            _ => return Ok(false),
        };
        self.validate_node_inputs(graph, node, limit)?;
        for &reference in &node.arguments {
            if reference.0 >= limit {
                return Err(internal!("fieldの依存が未出").into());
            }
            self.validate_at(graph, graph.get(reference)?, reference.0)?;
        }
        let source = *node
            .arguments
            .first()
            .ok_or(internal!("fieldの元Sourceがない"))?;
        let child = *node
            .arguments
            .get(1)
            .ok_or(internal!("fieldの実baseがない"))?;
        let origin = if matches!(graph.get(source)?.rule, Rule::FieldSource(_)) {
            let [origin, actual_child] = graph.get(source)?.arguments.as_slice() else {
                return Err(internal!("field read Sourceの依存数が違う").into());
            };
            if *actual_child != child {
                return Err(internal!("field read Sourceの実baseが違う").into());
            }
            *origin
        } else {
            source
        };
        let mut plan = self.field_read_observation(graph, origin, child, limit, |_, _| {})?;
        if plan.position.is_some() {
            if origin == source {
                return Err(internal!("実field readのSource carrierがない").into());
            }
            self.field_bind_read_source(&mut plan, source);
        }
        self.resolve_field_read(graph, &mut plan)?;
        let expected = if is_value {
            self.field_value_node(&plan)
                .ok_or(internal!("未確定fieldにScalarがある"))?
        } else {
            let Some(Payload::Evaluation { value, .. }) = &node.payload else {
                return Err(internal!("fieldのEvaluation payloadがない").into());
            };
            if let Some(reused) = plan.reused {
                if *value != Some(reused) {
                    return Err(internal!("fieldのArchitecture実refが違う").into());
                }
            } else if let Some(expected) = self.field_value_node(&plan) {
                let actual = value.ok_or(internal!("fieldのScalarがない"))?;
                if !graph
                    .get(actual)?
                    .matches_with_support(&expected, &self.control)?
                {
                    return Err(internal!("fieldのScalarが元read結果と違う").into());
                }
            } else if value.is_some() {
                return Err(internal!("未値fieldにScalarがある").into());
            }
            self.field_evaluation_node(graph, &plan, *value)?
        };
        if !node.matches_with_support(&expected, &self.control)? {
            return Err(internal!("fieldが元slot/実子/位置/Scopeと違う").into());
        }
        #[cfg(test)]
        data::observe_actual(
            plan.span,
            self.current_context(graph),
            "field_read_verified",
            usize::from(is_value),
        );
        Ok(true)
    }
}
