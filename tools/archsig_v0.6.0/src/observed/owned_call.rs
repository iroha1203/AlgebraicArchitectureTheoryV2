//! 単一Owned参照のcall境界を元署名・実引数・原始owner事実から検査する。
use super::*;
use crate::law::model::{Declaration, Signature};

#[derive(Default)]
pub(in crate::observed) struct Checks {
    pub scope: Scope,
    pub support: Vec<Fact>,
    pub failure: Option<(Scalar, Scalar)>,
    pub blocked: bool,
}

impl Environment<'_> {
    fn owned_reference_check(
        &self,
        ty: &Type,
        value: Option<&Scalar>,
        values: &BTreeMap<&str, Option<&Scalar>>,
        reading: &str,
        span: (usize, usize),
        checks: &mut Checks,
    ) -> Result<(), ValidationFailure> {
        let Type::Owned(entity, owner_name) = ty else {
            return Ok(());
        };
        self.tick()?;
        let unsupported = || ValidationFailure::UnsupportedExpression {
            location: Location::Law { span },
            feature: "未確定owner・実参照を持つview呼出しの所属条件".into(),
        };
        let expected = values.get(owner_name.as_str()).copied().flatten();
        let (Some(value), Some(expected)) = (value, expected) else {
            checks.blocked = true;
            return Ok(());
        };
        let Scalar::Subject {
            snapshot,
            subject,
            entity: actual_entity,
        } = value
        else {
            return Err("Owned callの実値が参照でない".into());
        };
        if actual_entity != entity {
            return Err("Owned callの参照型が元署名と違う".into());
        }
        let root = match &self
            .inputs
            .law()
            .definitions
            .declarations
            .get(entity)
            .ok_or("Owned callの原始型がない")?
            .signature
        {
            crate::definition::PrimitiveSignature::Entity {
                owner: Some(root), ..
            }
            | crate::definition::PrimitiveSignature::Arrow { owner: root, .. } => root,
            _ => return Err("Owned callの型がowned entity/arrowでない".into()),
        };
        if expected.ty() != Type::Ref(root.clone()) {
            return Err("Owned callの実owner型が元署名と違う".into());
        }
        let Scalar::Subject {
            snapshot: os,
            subject: oi,
            ..
        } = expected
        else {
            return Err("Owned callのownerが参照でない".into());
        };
        let subject_input = self.subject(snapshot, subject)?;
        checks
            .scope
            .merge(&self.scope(subject_input, reading, None)?);
        checks
            .scope
            .merge(&self.scope(self.subject(os, oi)?, reading, None)?);
        checks.support.extend([
            Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: None,
                atom: None,
            },
            Fact {
                snapshot: os.clone(),
                subject: oi.clone(),
                field: None,
                atom: None,
            },
        ]);
        let field = format!("{entity}.owner");
        let Slot::Known {
            value:
                Value::Ref {
                    snapshot: actual_snapshot,
                    subject: actual_subject,
                },
            atom,
            origin,
            ..
        } = &self.field(snapshot, subject, &field)?.slot
        else {
            return Err(unsupported());
        };
        checks
            .scope
            .merge(&self.scope(subject_input, reading, Some(origin))?);
        checks.support.push(Fact {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field: Some(field),
            atom: Some(atom.clone()),
        });
        let actual = Scalar::Subject {
            snapshot: actual_snapshot.clone(),
            subject: actual_subject.clone(),
            entity: root.clone(),
        };
        checks.scope.merge(&self.scope(
            self.subject(actual_snapshot, actual_subject)?,
            reading,
            None,
        )?);
        checks.support.push(Fact {
            snapshot: actual_snapshot.clone(),
            subject: actual_subject.clone(),
            field: None,
            atom: None,
        });
        if actual != *expected {
            checks.failure = Some((actual, expected.clone()));
        }
        #[cfg(test)]
        data::observe_actual(
            span,
            self.context.get().unwrap_or_default(),
            "owned_call_constraint",
            0,
        );
        self.tick()?;
        Ok(())
    }

    pub(in crate::observed) fn owned_call_checks(
        &self,
        declaration: &Declaration,
        arguments: &[Option<Scalar>],
        returned: Option<Option<&Scalar>>,
        span: (usize, usize),
    ) -> Result<Checks, ValidationFailure> {
        let Signature::View {
            params, returns, ..
        } = &declaration.signature
        else {
            return Err("Owned callの元宣言がviewでない".into());
        };
        if !matches!(returns, Type::Owned(..))
            && !params.iter().any(|p| matches!(p.ty, Type::Owned(..)))
        {
            return Ok(Checks::default());
        }
        if params.len() != arguments.len() {
            return Err("Owned callの引数数が元署名と違う".into());
        }
        let mut values = BTreeMap::new();
        let mut checks = Checks::default();
        for (p, value) in params.iter().zip(arguments) {
            self.tick()?;
            self.owned_reference_check(
                &p.ty,
                value.as_ref(),
                &values,
                &declaration.reading,
                span,
                &mut checks,
            )?;
            if checks.failure.is_some() || checks.blocked {
                break;
            }
            if values.insert(p.name.as_str(), value.as_ref()).is_some() {
                return Err("Owned callの元parameter名が重複する".into());
            }
        }
        if checks.failure.is_none()
            && !checks.blocked
            && let Some(value) = returned
        {
            self.owned_reference_check(
                returns,
                value,
                &values,
                &declaration.reading,
                span,
                &mut checks,
            )?;
        }
        checks.support.sort();
        checks.support.dedup();
        Ok(checks)
    }

    pub(super) fn owns_call(&self, id: usize) -> Result<bool, ValidationFailure> {
        let Some(d) = self.named_view(id)? else {
            return Ok(false);
        };
        let Signature::View {
            params, returns, ..
        } = &d.signature
        else {
            unreachable!()
        };
        Ok(matches!(returns, Type::Owned(..))
            || params.iter().any(|p| matches!(p.ty, Type::Owned(..))))
    }

    pub(in crate::observed) fn owned_call_inputs(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<Option<Checks>, ValidationFailure> {
        if !matches!(
            graph.get(source)?.payload,
            Some(Payload::Expression {
                location: Location::Law { .. },
                ..
            })
        ) {
            return Ok(None);
        }
        let span = self.expression_span(graph, source)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(None);
        };
        if !self.owns_call(id)? {
            return Ok(None);
        }
        let declaration = self.named_view(id)?.ok_or("Owned callの元targetがない")?;
        let Signature::View { params, body, .. } = &declaration.signature else {
            unreachable!()
        };
        let ExprKind::Call { args, .. } = &self.inputs.law().exprs[id].kind else {
            unreachable!()
        };
        if args.len() != params.len()
            || !(children.len() == args.len() || children.len() == args.len() + 1)
            || source.0 >= limit
            || graph.context_at(source.0) != self.current_context(graph)
        {
            return Err("Owned callの元引数数・Source Contextが違う".into());
        }
        self.validate_at(graph, graph.get(source)?, source.0)?;
        let bindings = self.expression_bindings(graph, source)?;
        let mut values = Vec::new();
        let mut scope = graph.get(source)?.scope.clone();
        let mut support = Vec::new();
        for (&id, &child) in args.iter().zip(children) {
            self.tick()?;
            if child.0 >= limit || graph.context_at(child.0) != self.current_context(graph) {
                return Err("Owned callの実引数が既出同callerでない".into());
            }
            self.recheck_evaluation(graph, child)?;
            let (expression, actual_bindings, value) = self.evaluation(graph, child)?;
            self.source_matches(graph, expression, id)?;
            if actual_bindings != bindings || self.actual_evaluation(graph, id, bindings)? != child
            {
                return Err("Owned callの引数producer・束縛が元出現と違う".into());
            }
            values.push(value.map(|r| graph.scalar(r).cloned()).transpose()?);
            scope.merge(&graph.get(child)?.scope);
            support.extend(graph.get(child)?.support.iter().cloned());
        }
        let mut checks = self.owned_call_checks(declaration, &values, None, span)?;
        if children.len() == args.len() + 1 {
            if checks.failure.is_some() || checks.blocked {
                return Err("所属不適合・未確定のcallee bodyを評価した".into());
            }
            let child = children[args.len()];
            if child.0 >= limit {
                return Err("Owned call bodyが未出".into());
            }
            let context = graph.context_at(child.0);
            let index = context.frame.ok_or("Owned call bodyにframeがない")?;
            let frame = graph.frames.get(index).ok_or("Owned call frameがない")?;
            if frame.source != source
                || frame.caller != self.current_context(graph)
                || frame.arguments != children[..args.len()]
                || context
                    != (super::super::call::Context {
                        frame: Some(index),
                        iteration: None,
                        ..frame.caller
                    })
            {
                return Err("Owned call bodyと元frameが違う".into());
            }
            if self.universal_source_root(graph, source)?.is_none() {
                self.frame_arguments(graph, index)?;
            }
            // 全域Sourceでは上のcaller/実引数対応と、以下の元Planからの
            // body再検査でframeを照合する。数値binderを通常の既知束縛へ落とさない。
            self.recheck_evaluation(graph, child)?;
            let (expression, _, value) = self.evaluation(graph, child)?;
            self.source_matches(graph, expression, *body)?;
            if graph.context_at(expression.0) != context {
                return Err("Owned body SourceのContextが違う".into());
            }
            checks = self.owned_call_checks(
                declaration,
                &values,
                Some(value.map(|r| graph.scalar(r)).transpose()?),
                span,
            )?;
            scope.merge(&graph.get(child)?.scope);
            support.extend(graph.get(child)?.support.iter().cloned());
        } else if checks.failure.is_none() && !checks.blocked {
            return Err("所属適合callに元body評価がない".into());
        }
        scope.merge(&checks.scope);
        support.extend(checks.support);
        support.sort();
        support.dedup();
        checks.scope = scope;
        checks.support = support;
        Ok(Some(checks))
    }

    pub(super) fn validate_owned_call_condition_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let extra = match (&node.payload, &node.rule) {
            (Some(Payload::OwnedCallCondition { .. }), _) => 3,
            (Some(Payload::OwnedCallCounterexample { .. }), _) => 2,
            (
                Some(Payload::Scalar(Scalar::Subject { .. })),
                Rule::Construction("evaluation" | "domain"),
            ) => 0,
            _ => return Ok(false),
        };
        let Some(n) = node.arguments.len().checked_sub(extra) else {
            return Err("Owned条件の元辺が不足".into());
        };
        if n == 0 {
            return Err("Owned条件に元Sourceがない".into());
        }
        let source = node.arguments[0];
        if !matches!(
            graph.get(source)?.payload,
            Some(Payload::Expression {
                location: Location::Law { .. },
                ..
            })
        ) {
            if extra == 0 {
                return Ok(false);
            }
            return Err("Owned条件に元call Sourceがない".into());
        }
        let Some(checks) = self.owned_call_inputs(graph, source, &node.arguments[1..n], limit)?
        else {
            if extra == 0 {
                return Ok(false);
            }
            return Err("Owned条件の元署名が違う".into());
        };
        let Some((actual, required)) = checks.failure else {
            if extra == 0 {
                return Ok(false);
            }
            return Err("Owned条件に元所属不適合がない".into());
        };
        if node.scope != checks.scope || node.support != checks.support || !node.reasons.is_empty()
        {
            return Err("Owned条件の元Scope・支持・理由が違う".into());
        }
        match &node.payload {
            Some(Payload::Scalar(value)) => {
                let expected = match node.rule {
                    Rule::Construction("evaluation") => &actual,
                    Rule::Construction("domain") => &required,
                    _ => return Err("Owned条件owner値の規則が違う".into()),
                };
                if value != expected
                    || node.ty != NodeType::Value(expected.ty())
                    || !node.evidence.is_empty()
                    || node.judgment.is_some()
                {
                    return Err("Owned条件owner値が原始所属・実引数と違う".into());
                }
            }
            Some(Payload::OwnedCallCounterexample {
                bindings,
                left,
                right,
                ..
            }) => {
                graph.owned_call_counterexample_shape(node)?;
                if bindings != self.expression_bindings(graph, source)?
                    || node.arguments[n..] != [*left, *right]
                {
                    return Err("Owned反例の元束縛・辺が違う".into());
                }
                for r in [*left, *right] {
                    self.validate_at(graph, graph.get(r)?, r.0)?;
                }
                if graph.scalar(*left)? != &actual || graph.scalar(*right)? != &required {
                    return Err("Owned反例が元owner不等でない".into());
                }
            }
            Some(Payload::OwnedCallCondition { left, right }) => {
                if node.ty != NodeType::Proposition || node.arguments[n..n + 2] != [*left, *right] {
                    return Err("Owned条件命題の型・辺が違う".into());
                }
                graph.validate_proposition_evidence(node)?;
                for r in [*left, *right, node.arguments[n + 2]] {
                    self.validate_at(graph, graph.get(r)?, r.0)?;
                }
                if graph.scalar(*left)? != &actual || graph.scalar(*right)? != &required {
                    return Err("Owned条件命題の実ownerが違う".into());
                }
            }
            _ => return Err("Owned条件payloadが違う".into()),
        }
        Ok(true)
    }

    pub(super) fn owned_call_condition_reason(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<Option<Reason>, ValidationFailure> {
        let Some(checks) = self.owned_call_inputs(graph, source, children, limit)? else {
            return Ok(None);
        };
        if checks.failure.is_none() {
            return Ok(None);
        }
        let edges: Vec<_> = std::iter::once(source)
            .chain(children.iter().copied())
            .collect();
        let mut found = None;
        for (i, node) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if graph.context_at(i) == self.current_context(graph)
                && matches!(node.payload, Some(Payload::OwnedCallCondition { .. }))
                && node.arguments.get(..edges.len()) == Some(edges.as_slice())
            {
                self.validate_at(graph, node, i)?;
                if found.replace(NodeRef(i)).is_some() {
                    return Err("元callの所属条件命題が重複".into());
                }
            }
        }
        let condition = found.ok_or("元callの反証済み所属条件がない")?;
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("Owned条件の元requestがない")?;
        Ok(Some(Reason {
            kind: ReasonKind::ConditionFailed {
                condition,
                construction: "evaluation",
            },
            request: request.id.clone(),
            dependencies: vec![source],
            missing: vec![],
            location: Some(Location::Law {
                span: self.expression_span(graph, source)?,
            }),
        }))
    }

    pub(super) fn validate_failed_owned_call(
        &self,
        graph: &Graph,
        node: &Node,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if !matches!(
            graph.get(source)?.payload,
            Some(Payload::Expression {
                location: Location::Law { .. },
                ..
            })
        ) {
            return Ok(false);
        }
        let span = self.expression_span(graph, source)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(false);
        };
        if !self.owns_call(id)? {
            return Ok(false);
        }
        let Some(declaration) = self.named_view(id)? else {
            return Ok(false);
        };
        let Signature::View { params, .. } = &declaration.signature else {
            unreachable!()
        };
        if children.len() != params.len() && children.len() != params.len() + 1 {
            return Ok(false);
        }
        let checks = self
            .owned_call_inputs(graph, source, children, limit)?
            .ok_or("Owned callの元条件がない")?;
        if checks.failure.is_none() && !checks.blocked {
            return Ok(false);
        }
        let Some(Payload::Evaluation {
            expression,
            bindings,
            parts,
            value,
            applicability,
        }) = &node.payload
        else {
            return Ok(false);
        };
        let expected: Vec<_> = std::iter::once(source)
            .chain(children.iter().copied())
            .collect();
        if *expression != source
            || bindings != self.expression_bindings(graph, source)?
            || value.is_some()
            || *applicability != "applicable"
            || parts.len() != 1
            || parts[0].location != (Location::Law { span })
            || parts[0].value.is_some()
            || parts[0].residual.is_some()
            || node.arguments != expected
            || node.ty
                != NodeType::Evaluation(
                    self.inputs
                        .law()
                        .expr_type(id)
                        .ok_or("Owned callの元型がない")?
                        .clone(),
                )
            || node.support != checks.support
            || node.scope != checks.scope
            || !node.evidence.is_empty()
            || node.judgment.is_some()
            || !matches!(node.rule, Rule::Construction("evaluation"))
        {
            return Err("所属不適合call評価の元辺・値・型・Scopeが違う".into());
        }
        self.evaluation_missing_reasons(graph, node, source, children, None)?;
        Ok(true)
    }
}
