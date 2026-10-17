//! 数値parameterの型全域を、欠測slotの補完と区別して元式から評価する。
use super::*;
use crate::observed::{affine::CompletionPair, environment::universal::UniversalPlan};

#[derive(Clone)]
struct SymbolicEvaluation {
    evaluated: Evaluated,
    comparison: Option<(usize, Evaluated, Evaluated, NodeRef)>,
    has_local_domains: bool,
}

pub(super) struct UniversalEvaluation {
    pub evaluated: Evaluated,
    pub evidence: Vec<NodeRef>,
    pub body: NodeRef,
    pub guard: Option<NodeRef>,
}

struct NumericCompletion<'a> {
    plan: &'a UniversalPlan,
    template: NodeRef,
    domains: &'a [NodeRef],
    body: &'a Evaluated,
    residual: NodeRef,
    reasons: &'a [Reason],
    support: &'a [Fact],
    original_scope: &'a Scope,
}

struct CounterexampleContext<'a> {
    template: NodeRef,
    domains: &'a [NodeRef],
    support: &'a [Fact],
    scope: &'a Scope,
}

impl Evaluator<'_, '_> {
    fn universal_numeric_pair(
        &mut self,
        context: NumericCompletion<'_>,
        pair: &CompletionPair,
    ) -> Result<Option<NodeRef>, Failure> {
        let pair = (
            self.environment.restore_numeric_assignment(&pair.0)?,
            self.environment.restore_numeric_assignment(&pair.1)?,
        );
        let NumericCompletion {
            plan,
            template,
            domains,
            body,
            residual,
            reasons,
            support,
            original_scope,
        } = context;
        let mut fields = BTreeMap::new();
        for reason in reasons {
            self.tick(Checkpoint::FiniteIteration)?;
            if matches!(reason.kind, ReasonKind::Missing) {
                for fact in &reason.missing {
                    if let Some(&source) = reason.dependencies.first()
                        && let NodeType::Expression(ty) = &self.graph.get(source)?.ty
                        && numeric::is_numeric_type(ty, self.control)?
                    {
                        fields.entry(fact.clone()).or_insert((source, ty.clone()));
                    }
                }
            }
        }
        if fields.is_empty() {
            return Err(Failure::Internal("数値補完対の元欠測slotがない".into()));
        }
        let parameters = match &self.graph.get(template)?.payload {
            Some(
                Payload::Expression { parameters, .. }
                | Payload::ParameterizedTransform { parameters, .. },
            ) => parameters.clone(),
            _ => {
                return Err(Failure::Internal(
                    "数値補完対の元自由parameterがない".into(),
                ));
            }
        };
        let mut scope = original_scope.clone();
        scope.completions = true;
        let mut anchors = Vec::new();
        let mut assignments = Vec::new();
        let mut results = Vec::new();
        let mut booleans = Vec::new();
        for (ordinal, values) in [&pair.0, &pair.1].into_iter().enumerate() {
            self.universal_observe(plan.template_span, 5)?;
            let anchor_ref = NodeRef(self.graph.nodes.len());
            self.graph.universal_witnesses.push(UniversalWitness {
                caller: self.graph.active,
                template,
                anchor: anchor_ref,
                ordinal,
            });
            let anchor_result = self.push(Node {
                ty: NodeType::Expression(Type::Bool),
                payload: Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Substitute,
                    operands: vec![template],
                    parameters: parameters.clone(),
                    bindings: self.bindings.clone(),
                }),
                rule: Rule::Construction("expression"),
                arguments: std::iter::once(template)
                    .chain(self.bindings.iter().map(|binding| binding.value))
                    .collect(),
                support: support.to_vec(),
                evidence: vec![],
                judgment: None,
                scope: scope.clone(),
                reasons: vec![],
            });
            let anchor = match anchor_result {
                Ok(anchor) => anchor,
                Err(error) => {
                    if self.graph.nodes.len() == anchor_ref.0 {
                        self.graph.universal_witnesses.pop();
                    }
                    return Err(error);
                }
            };
            let mut references = Vec::new();
            let mut facts = Vec::new();
            for (fact, (source, ty)) in &fields {
                self.tick(Checkpoint::FiniteIteration)?;
                let value = match values.iter().find(|(candidate, _)| candidate == fact) {
                    Some((_, value)) => value.clone(),
                    None => numeric::zero(ty, self.control)?,
                };
                facts.push((fact.clone(), value.clone()));
                references.push(self.value(
                    value,
                    Rule::Construction("evaluation"),
                    vec![template, anchor, *source],
                    vec![],
                    scope.clone(),
                )?);
            }
            let recomputed = self
                .environment
                .universal_completion_analysis(self.graph, template, domains, &facts)?;
            let Some(boolean) = recomputed.value else {
                return Ok(None);
            };
            let value = self.value(
                Scalar::Bool(boolean),
                Rule::Construction("evaluation"),
                vec![template, anchor]
                    .into_iter()
                    .chain(references.iter().copied())
                    .collect(),
                support.to_vec(),
                scope.clone(),
            )?;
            let evaluation = self.push(Node {
                ty: NodeType::Evaluation(Type::Bool),
                payload: Some(Payload::Evaluation {
                    expression: anchor,
                    bindings: self.bindings.clone(),
                    parts: vec![Part {
                        location: Location::Law {
                            span: plan.template_span,
                        },
                        value: Some(value),
                        residual: Some(residual),
                        children: vec![body.evaluation],
                    }],
                    value: Some(value),
                    applicability: "applicable",
                }),
                rule: Rule::Construction("evaluation"),
                arguments: std::iter::once(anchor)
                    .chain(domains.iter().copied())
                    .chain([body.evaluation, residual])
                    .chain(references.iter().copied())
                    .chain([value])
                    .collect(),
                support: support.to_vec(),
                evidence: vec![],
                judgment: None,
                scope: scope.clone(),
                reasons: reasons.to_vec(),
            })?;
            anchors.push(anchor);
            assignments.push(references);
            results.push(evaluation);
            booleans.push(boolean);
        }
        if booleans[0] == booleans[1] {
            return Ok(None);
        }
        let fields = fields.into_keys().collect();
        let pair = self.push(Node {
            ty: NodeType::Evidence,
            payload: Some(Payload::CompletionPair {
                fields,
                first: assignments[0].clone(),
                second: assignments[1].clone(),
                first_result: results[0],
                second_result: results[1],
            }),
            rule: Rule::Construction("evidence"),
            arguments: vec![template, anchors[0], anchors[1], results[0], results[1]]
                .into_iter()
                .chain(assignments.into_iter().flatten())
                .collect(),
            support: support.to_vec(),
            evidence: vec![],
            judgment: None,
            scope,
            reasons: vec![],
        })?;
        self.universal_observe(plan.template_span, 6)?;
        Ok(Some(pair))
    }
    fn universal_substitute_expression(
        &mut self,
        original: NodeRef,
        bindings: &[Binding],
        template: NodeRef,
        domains: &[NodeRef],
    ) -> Result<(NodeRef, SourceAnalysis), Failure> {
        let analyzed = self
            .environment
            .universal_substitution_analysis(self.graph, original, bindings, template, domains)?;
        let NodeType::Expression(ty) = &self.graph.get(original)?.ty else {
            return Err(Failure::Internal("全域代入の元型がない".into()));
        };
        let node = Node {
            ty: NodeType::Expression(ty.clone()),
            payload: Some(Payload::ParameterizedTransform {
                operation: TransformOp::Substitute,
                operands: vec![original],
                parameters: analyzed.parameters,
                bindings: bindings.to_vec(),
            }),
            rule: Rule::Construction("expression"),
            arguments: std::iter::once(original)
                .chain(bindings.iter().map(|binding| binding.value))
                .collect(),
            support: analyzed.analysis.support.clone(),
            evidence: vec![],
            judgment: None,
            scope: analyzed.analysis.scope.clone(),
            reasons: vec![],
        };
        let expression = self.push(node)?;
        Ok((expression, analyzed.analysis))
    }

    fn universal_substitute_evaluation(
        &mut self,
        original: &Evaluated,
        bindings: &[Binding],
        template: NodeRef,
        domains: &[NodeRef],
    ) -> Result<NodeRef, Failure> {
        let (expression, analysis) =
            self.universal_substitute_expression(original.expression, bindings, template, domains)?;
        let value = analysis
            .known_value
            .map(|known| {
                self.value(
                    known,
                    Rule::Construction("evaluation"),
                    vec![expression, original.evaluation],
                    analysis.support.clone(),
                    analysis.scope.clone(),
                )
            })
            .transpose()?;
        let NodeType::Evaluation(ty) = &self.graph.get(original.evaluation)?.ty else {
            unreachable!()
        };
        let Some(Payload::Evaluation { parts, .. }) = &self.graph.get(original.evaluation)?.payload
        else {
            unreachable!()
        };
        let location = parts[0].location.clone();
        self.push(Node {
            ty: NodeType::Evaluation(ty.clone()),
            payload: Some(Payload::Evaluation {
                expression,
                bindings: bindings.to_vec(),
                parts: vec![Part {
                    location,
                    value,
                    residual: None,
                    children: vec![original.evaluation],
                }],
                value,
                applicability: "applicable",
            }),
            rule: Rule::Construction("evaluation"),
            arguments: vec![expression, original.evaluation]
                .into_iter()
                .chain(value)
                .collect(),
            support: analysis.support,
            evidence: vec![],
            judgment: None,
            scope: analysis.scope,
            reasons: original.reasons.clone(),
        })
    }

    fn universal_counterexample_values(
        &mut self,
        original: NodeRef,
        context: &CounterexampleContext<'_>,
        shared: &[Binding],
    ) -> Result<Vec<Binding>, Failure> {
        let mut bindings = match &self.graph.get(original)?.payload {
            Some(Payload::Expression { bindings, .. }) => bindings.clone(),
            _ => return Err(Failure::Internal("全域反例の元EqSourceがない".into())),
        };
        for (name, ty, value, binder) in self.environment.universal_counterexample_bindings(
            self.graph,
            original,
            context.template,
            context.domains,
        )? {
            let mut inherited = None;
            for candidate in shared {
                self.tick(Checkpoint::FiniteIteration)?;
                let producer = self.graph.get(candidate.value)?;
                if candidate.name == name
                    && candidate.ty == ty
                    && self.graph.scalar(candidate.value)? == &value
                    && matches!(&producer.rule,Rule::Input {kind:"law",location:Location::Law {span}} if *span==binder)
                    && producer.arguments.first() == Some(&context.template)
                    && producer.arguments.get(1).is_some_and(|source| {
                        self.graph.context_at(source.0) == self.graph.context_at(original.0)
                    })
                {
                    inherited = Some(candidate.value);
                    break;
                }
            }
            let value = if let Some(value) = inherited {
                value
            } else {
                self.value(
                    value,
                    Rule::Input {
                        kind: "law",
                        location: Location::Law { span: binder },
                    },
                    vec![context.template, original],
                    context.support.to_vec(),
                    context.scope.clone(),
                )?
            };
            bindings.push(Binding { name, ty, value });
        }
        Ok(bindings)
    }

    fn universal_counterexample_substitution(
        &mut self,
        original: NodeRef,
        comparison: &(usize, Evaluated, Evaluated, NodeRef),
        template: NodeRef,
        domains: &[NodeRef],
        support: &[Fact],
        scope: &Scope,
    ) -> Result<(NodeRef, Vec<Binding>, NodeRef, NodeRef), Failure> {
        let context = CounterexampleContext {
            template,
            domains,
            support,
            scope,
        };
        let bindings = self.universal_counterexample_values(original, &context, &[])?;
        let (body, _) =
            self.universal_substitute_expression(original, &bindings, template, domains)?;
        let left_bindings = if self.universal_counterexample_shares_bindings(
            comparison.1.expression,
            original,
            template,
            domains,
        )? {
            bindings.clone()
        } else {
            self.universal_counterexample_values(comparison.1.expression, &context, &bindings)?
        };
        let right_bindings = if self.universal_counterexample_shares_bindings(
            comparison.2.expression,
            original,
            template,
            domains,
        )? {
            bindings.clone()
        } else {
            self.universal_counterexample_values(comparison.2.expression, &context, &bindings)?
        };
        let left =
            self.universal_substitute_evaluation(&comparison.1, &left_bindings, template, domains)?;
        let right = self.universal_substitute_evaluation(
            &comparison.2,
            &right_bindings,
            template,
            domains,
        )?;
        Ok((body, bindings, left, right))
    }

    fn universal_counterexample_shares_bindings(
        &self,
        side: NodeRef,
        original: NodeRef,
        template: NodeRef,
        domains: &[NodeRef],
    ) -> Result<bool, Failure> {
        if self.graph.context_at(side.0) != self.graph.context_at(original.0) {
            return Ok(false);
        }
        let (
            Some(Payload::Expression {
                bindings: side_bindings,
                ..
            }),
            Some(Payload::Expression {
                bindings: original_bindings,
                ..
            }),
        ) = (
            &self.graph.get(side)?.payload,
            &self.graph.get(original)?.payload,
        )
        else {
            return Err(Failure::Internal("全域反例の共有元Sourceがない".into()));
        };
        Ok(side_bindings == original_bindings
            && self
                .environment
                .universal_counterexample_bindings(self.graph, side, template, domains)?
                == self
                    .environment
                    .universal_counterexample_bindings(self.graph, original, template, domains)?)
    }
    fn universal_raw_source(
        &mut self,
        plan: &UniversalPlan,
        span: (usize, usize),
    ) -> Result<(NodeRef, SourceAnalysis), Failure> {
        let analyzed = self.environment.universal_template_source_analysis(
            self.graph,
            plan,
            span,
            &self.bindings,
        )?;
        self.retained_scope.merge(&analyzed.analysis.scope);
        let analysis = analyzed.analysis.clone();
        let source = self.push(Node {
            ty: NodeType::Expression(Type::Bool),
            payload: Some(Payload::Expression {
                location: Location::Law { span },
                parameters: analyzed.parameters,
                bindings: self.bindings.clone(),
            }),
            rule: Rule::Input {
                kind: "law",
                location: Location::Law { span },
            },
            arguments: self
                .environment
                .source_arguments(self.graph, span, &self.bindings)?,
            support: vec![],
            evidence: vec![],
            judgment: None,
            scope: analyzed.analysis.scope,
            reasons: vec![],
        })?;
        Ok((source, analysis))
    }

    fn universal_conditional_transform(
        &mut self,
        operation: TransformOp,
        operands: Vec<NodeRef>,
        parameters: &[(String, Type)],
        scope: &Scope,
        support: &[Fact],
    ) -> Result<NodeRef, Failure> {
        self.push(Node {
            ty: NodeType::Expression(Type::Bool),
            payload: Some(Payload::ParameterizedTransform {
                operation,
                operands: operands.clone(),
                parameters: parameters.to_vec(),
                bindings: self.bindings.clone(),
            }),
            rule: Rule::Construction("expression"),
            arguments: operands
                .into_iter()
                .chain(self.bindings.iter().map(|binding| binding.value))
                .collect(),
            support: support.to_vec(),
            evidence: vec![],
            judgment: None,
            scope: scope.clone(),
            reasons: vec![],
        })
    }

    fn universal_template(
        &mut self,
        plan: &UniversalPlan,
    ) -> Result<(NodeRef, NodeRef, Option<NodeRef>), Failure> {
        let (body, body_analysis) = self.universal_raw_source(plan, plan.template_span)?;
        let Some(guard) = plan.guard else {
            return Ok((body, body, None));
        };
        let guard_span = self.environment.inputs.law().exprs[guard].span;
        let (guard, guard_analysis) = self.universal_raw_source(plan, guard_span)?;
        let Some(Payload::Expression { parameters, .. }) = &self.graph.get(body)?.payload else {
            unreachable!()
        };
        let parameters = parameters.clone();
        let mut scope = self.graph.get(body)?.scope.clone();
        scope.merge(&self.graph.get(guard)?.scope);
        let mut support = guard_analysis.support;
        if guard_analysis.known_value != Some(Scalar::Bool(false)) {
            support.extend(body_analysis.support.iter().cloned());
        }
        support.sort();
        support.dedup();
        let not_body = self.universal_conditional_transform(
            TransformOp::Not,
            vec![body],
            &parameters,
            &scope,
            &body_analysis.support,
        )?;
        let conjunction = self.universal_conditional_transform(
            TransformOp::And,
            vec![guard, not_body],
            &parameters,
            &scope,
            &support,
        )?;
        let template = self.universal_conditional_transform(
            TransformOp::Not,
            vec![conjunction],
            &parameters,
            &scope,
            &support,
        )?;
        Ok((template, body, Some(guard)))
    }

    pub(super) fn universal_evaluation(
        &mut self,
        plan: UniversalPlan,
    ) -> Result<UniversalEvaluation, Failure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.universal_evaluation_inner(plan)
        })
    }

    #[inline(never)]
    fn universal_evaluation_inner(
        &mut self,
        plan: UniversalPlan,
    ) -> Result<UniversalEvaluation, Failure> {
        let (template, raw_body, raw_guard) = self.universal_template(&plan)?;
        let mut domains = Vec::new();
        for parameter in &plan.parameters {
            self.universal_observe(plan.template_span, 0)?;
            domains.push(self.push(Node {
                ty: NodeType::Domain,
                payload: Some(Payload::TypeDomain {
                    ty: parameter.kind.ty(),
                }),
                rule: Rule::Input {
                    kind: "law",
                    location: Location::Law {
                        span: parameter.binder,
                    },
                },
                arguments: vec![template],
                support: vec![],
                evidence: vec![],
                judgment: None,
                scope: self.graph.get(template)?.scope.clone(),
                reasons: vec![],
            })?);
        }
        let analyzed =
            self.environment
                .universal_analysis(self.graph, template, &domains, &self.bindings)?;
        let guard = plan
            .guard
            .map(|id| self.universal_pointwise(&plan, template, &domains, id))
            .transpose()?;
        let body = if analyzed.guard_value == Some(false) {
            None
        } else {
            let id = self
                .environment
                .inputs
                .law()
                .exprs
                .iter()
                .position(|expression| expression.span == plan.template_span)
                .ok_or_else(|| Failure::Internal("全域templateの元ASTがない".into()))?;
            Some(self.universal_pointwise(&plan, template, &domains, id)?)
        };
        let analyzed = if guard
            .iter()
            .chain(body.iter())
            .any(|value| value.has_local_domains)
        {
            self.environment
                .universal_analysis(self.graph, template, &domains, &self.bindings)?
        } else {
            analyzed
        };
        let scope = analyzed.analysis.scope.clone();
        let support = analyzed.analysis.support.clone();
        self.retained_scope.merge(&scope);
        let mut steps = Vec::new();
        let mut residual = None;
        if let Some(body) = &body {
            if let (Some(expected), Some((id, left, right, _))) =
                (analyzed.comparison_expression, body.comparison.clone())
            {
                if expected != id {
                    return Err(Failure::Internal(
                        "全域の実比較producerが元最終比較と違う".into(),
                    ));
                }
                let ty = match &self.graph.get(left.evaluation)?.ty {
                    NodeType::Evaluation(ty) => ty.clone(),
                    _ => return Err(Failure::Internal("全域比較の左型がない".into())),
                };
                let Some(Payload::Expression { parameters, .. }) =
                    &self.graph.get(left.expression)?.payload
                else {
                    unreachable!()
                };
                let difference = self.push(Node {
                    ty: NodeType::Expression(ty.clone()),
                    payload: Some(Payload::ParameterizedTransform {
                        operation: TransformOp::Difference,
                        operands: vec![left.expression, right.expression],
                        parameters: parameters.clone(),
                        bindings: self.bindings.clone(),
                    }),
                    rule: Rule::Construction("expression"),
                    arguments: std::iter::once(template)
                        .chain(domains.iter().copied())
                        .chain([left.evaluation, right.evaluation])
                        .collect(),
                    support: support.clone(),
                    evidence: vec![],
                    judgment: None,
                    scope: scope.clone(),
                    reasons: vec![],
                })?;
                steps.push(difference);
                let value = analyzed
                    .classification
                    .as_ref()
                    .map(|classification| classification.difference.value(self.control))
                    .transpose()?
                    .flatten()
                    .map(|known| {
                        self.value(
                            known,
                            Rule::Construction("evaluation"),
                            vec![difference, left.evaluation, right.evaluation],
                            support.clone(),
                            scope.clone(),
                        )
                    })
                    .transpose()?;
                let span = self.environment.inputs.law().exprs[id].span;
                let mut reasons = left.reasons.clone();
                reasons.extend(right.reasons.iter().cloned());
                sort_reasons(&mut reasons);
                residual = Some(
                    self.push(Node {
                        ty: NodeType::Evaluation(ty),
                        payload: Some(Payload::Evaluation {
                            expression: difference,
                            bindings: self.bindings.clone(),
                            parts: vec![Part {
                                location: Location::Law { span },
                                value,
                                residual: None,
                                children: vec![left.evaluation, right.evaluation],
                            }],
                            value,
                            applicability: "applicable",
                        }),
                        rule: Rule::Construction("evaluation"),
                        arguments: vec![difference, left.evaluation, right.evaluation]
                            .into_iter()
                            .chain(value)
                            .collect(),
                        support: support.clone(),
                        evidence: vec![],
                        judgment: None,
                        scope: scope.clone(),
                        reasons,
                    })?,
                );
                self.universal_observe(plan.template_span, 1)?;
            }
        } else if let Some(guard) = raw_guard {
            steps.push(guard);
        }
        let mut reasons = body
            .as_ref()
            .map(|body| body.evaluated.reasons.clone())
            .unwrap_or_default();
        if let Some(guard) = &guard {
            reasons.extend(guard.evaluated.reasons.iter().cloned());
        }
        sort_reasons(&mut reasons);
        if analyzed.value.is_none()
            && !reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            && (analyzed.classification.is_none()
                || (plan.guard.is_some() && analyzed.guard_value.is_none()))
        {
            let mut operand_types = plan
                .parameters
                .iter()
                .map(|parameter| parameter.kind.ty())
                .collect::<Vec<_>>();
            operand_types.dedup();
            reasons.push(Reason {
                kind: ReasonKind::UnsupportedAlgorithm {
                    question: self.request.kind,
                    operand_types,
                    method: if plan.guard.is_some() && analyzed.guard_value.is_none() {
                        "parameter-dependent conditional affine equality".into()
                    } else {
                        "non-affine universal equality".into()
                    },
                },
                request: self.request.id.clone(),
                dependencies: vec![template],
                missing: vec![],
                location: Some(Location::Law {
                    span: plan.template_span,
                }),
            });
            sort_reasons(&mut reasons);
        }
        let concrete = if analyzed.value == Some(false)
            && analyzed
                .classification
                .as_ref()
                .is_some_and(|classification| classification.common_counterexample.is_some())
        {
            let comparison = body
                .as_ref()
                .and_then(|body| body.comparison.as_ref())
                .ok_or_else(|| Failure::Internal("全域共通反例の元比較がない".into()))?;
            let original_span = self.environment.inputs.law().exprs[plan.body].span;
            let original=self.graph.nodes.iter().enumerate().find_map(|(index,node)| {
                (self.graph.context_at(index)==self.graph.active && node.arguments.first()==Some(&template)
                    && matches!(&node.payload,Some(Payload::Expression {location:Location::Law{span},..}) if *span==original_span)).then_some(NodeRef(index))
            }).ok_or_else(||Failure::Internal("全域共通反例の元body Sourceがない".into()))?;
            let concrete = self.universal_counterexample_substitution(
                original, comparison, template, &domains, &support, &scope,
            )?;
            steps.push(concrete.0);
            Some(concrete)
        } else {
            None
        };
        let value = analyzed
            .value
            .map(|known| {
                self.value(
                    Scalar::Bool(known),
                    Rule::Construction("evaluation"),
                    std::iter::once(template)
                        .chain(steps.iter().copied())
                        .collect(),
                    support.clone(),
                    scope.clone(),
                )
            })
            .transpose()?;
        self.universal_observe(plan.template_span, 2)?;
        let normalization = value
            .map(|after| {
                self.push(Node {
                    ty: NodeType::Evidence,
                    payload: Some(Payload::Normalization {
                        before: template,
                        after,
                        steps: steps.clone(),
                    }),
                    rule: Rule::Construction("evidence"),
                    arguments: vec![template, after]
                        .into_iter()
                        .chain(steps.iter().copied())
                        .collect(),
                    support: support.clone(),
                    evidence: vec![],
                    judgment: None,
                    scope: scope.clone(),
                    reasons: vec![],
                })
            })
            .transpose()?;
        self.universal_observe(plan.template_span, 3)?;
        let pair = if analyzed.value.is_none()
            && (plan.guard.is_none() || analyzed.guard_value == Some(true))
        {
            if let (Some(body), Some(residual), Some(pair)) = (
                body.as_ref(),
                residual,
                analyzed
                    .classification
                    .as_ref()
                    .and_then(|classification| classification.completion_pair.as_ref()),
            ) {
                self.universal_numeric_pair(
                    NumericCompletion {
                        plan: &plan,
                        template,
                        domains: &domains,
                        body: &body.evaluated,
                        residual,
                        reasons: &reasons,
                        support: &support,
                        original_scope: &scope,
                    },
                    pair,
                )?
            } else {
                None
            }
        } else {
            None
        };
        let applicability = if raw_guard.is_none() || analyzed.guard_value == Some(true) {
            "applicable"
        } else if analyzed.guard_value == Some(false) {
            "not_applicable"
        } else {
            "undetermined"
        };
        let mut parts = Vec::new();
        if let Some(guard) = &guard {
            parts.push(Part {
                location: Location::Law {
                    span: self.environment.inputs.law().exprs[plan.guard.unwrap()].span,
                },
                value: guard.evaluated.value,
                residual: None,
                children: vec![guard.evaluated.evaluation],
            });
        }
        parts.push(Part {
            location: Location::Law {
                span: plan.template_span,
            },
            value: if raw_guard.is_some() {
                body.as_ref().and_then(|body| body.evaluated.value)
            } else {
                value
            },
            residual,
            children: body.iter().map(|body| body.evaluated.evaluation).collect(),
        });
        let evaluation = self.push(Node {
            ty: NodeType::Evaluation(Type::Bool),
            payload: Some(Payload::Evaluation {
                expression: template,
                bindings: self.bindings.clone(),
                parts,
                value,
                applicability,
            }),
            rule: Rule::Construction("evaluation"),
            arguments: std::iter::once(template)
                .chain(domains.iter().copied())
                .chain(guard.iter().map(|guard| guard.evaluated.evaluation))
                .chain(body.iter().map(|body| body.evaluated.evaluation))
                .chain(residual)
                .chain(value)
                .chain(normalization)
                .chain(pair)
                .collect(),
            support: support.clone(),
            evidence: normalization.into_iter().chain(pair).collect(),
            judgment: None,
            scope: scope.clone(),
            reasons: reasons.clone(),
        })?;
        let mut evidence = normalization.into_iter().chain(pair).collect::<Vec<_>>();
        if analyzed.value == Some(false) {
            let normalization = normalization
                .ok_or_else(|| Failure::Internal("全域反証に正規化証拠がない".into()))?;
            let value =
                value.ok_or_else(|| Failure::Internal("全域反証にwholefalse値がない".into()))?;
            let (bindings, left, right, arguments) =
                if let Some((substitute, bindings, left, right)) = concrete {
                    (
                        bindings,
                        left,
                        right,
                        vec![template, normalization, substitute, left, right],
                    )
                } else {
                    let truth = self.value(
                        Scalar::Bool(true),
                        Rule::Construction("proposition"),
                        vec![template, evaluation, normalization],
                        vec![],
                        scope.clone(),
                    )?;
                    (
                        self.bindings.clone(),
                        value,
                        truth,
                        vec![template, evaluation, normalization],
                    )
                };
            let counterexample = self.push(Node {
                ty: NodeType::Evidence,
                payload: Some(Payload::Counterexample {
                    bindings,
                    left,
                    right,
                    facts: support.clone(),
                }),
                rule: Rule::Construction("evidence"),
                arguments,
                support: support.clone(),
                evidence: vec![],
                judgment: None,
                scope: scope.clone(),
                reasons: vec![],
            })?;
            evidence.push(counterexample);
            self.universal_observe(plan.template_span, 4)?;
        }
        let evaluated = Evaluated {
            expression: template,
            evaluation,
            value,
            scope,
            support,
            reasons,
            comparison: None,
            residual,
        };
        Ok(UniversalEvaluation {
            evaluated,
            evidence,
            body: raw_body,
            guard: raw_guard,
        })
    }

    pub(super) fn universal_family_answer(
        &mut self,
        params: &[Param],
        role: Option<Role>,
    ) -> Result<Answer, Failure> {
        let fixed = params
            .iter()
            .filter(|parameter| {
                self.request
                    .arguments
                    .iter()
                    .any(|argument| argument.name == format!("bind.{}", parameter.name))
            })
            .cloned()
            .collect::<Vec<_>>();
        self.bind(&fixed)?;
        let plan = self
            .environment
            .universal_family_plan(self.graph, self.request, &self.bindings)?
            .ok_or_else(|| Failure::Internal("数値Law全域の計画がない".into()))?;
        self.universal_law_answer(plan, role)
    }

    pub(super) fn universal_law_answer(
        &mut self,
        plan: UniversalPlan,
        role: Option<Role>,
    ) -> Result<Answer, Failure> {
        let result = self.universal_evaluation(plan)?;
        let evaluated = result.evaluated;
        self.answer_evaluation = Some(evaluated.evaluation);
        let status = match evaluated
            .value
            .map(|value| self.graph.scalar(value))
            .transpose()?
        {
            Some(Scalar::Bool(true)) => Decision::Established,
            Some(Scalar::Bool(false)) => Decision::Refuted,
            _ => Decision::Undetermined,
        };
        let instance = self.push(Node {
            ty: NodeType::LawInstance,
            payload: Some(Payload::LawInstance {
                name: self.declaration.name.clone(),
                role: match role
                    .ok_or_else(|| Failure::Internal("数値全域Law roleがない".into()))?
                {
                    Role::Required => "required",
                    Role::Optional => "optional",
                },
                bindings: self.bindings.clone(),
                guard: result.guard,
                body: result.body,
                occurrence: Location::Law {
                    span: self.declaration.span,
                },
            }),
            rule: Rule::Construction("law_instance"),
            arguments: vec![evaluated.evaluation]
                .into_iter()
                .chain(self.bindings.iter().map(|binding| binding.value))
                .collect(),
            support: evaluated.support.clone(),
            evidence: vec![],
            judgment: None,
            scope: evaluated.scope.clone(),
            reasons: vec![],
        })?;
        let proposition = self.push(Node {
            ty: NodeType::Proposition,
            payload: Some(Payload::Proposition { instance }),
            rule: Rule::Construction("proposition"),
            arguments: vec![instance, evaluated.evaluation],
            support: evaluated.support.clone(),
            evidence: result.evidence.clone(),
            judgment: Some(Judgment {
                status,
                evidence: result.evidence.clone(),
                reasons: evaluated.reasons.clone(),
            }),
            scope: evaluated.scope.clone(),
            reasons: evaluated.reasons.clone(),
        })?;
        Ok(Answer {
            id: self.request.id.clone(),
            status,
            outputs: BTreeMap::from([
                ("evaluation".into(), evaluated.evaluation),
                ("proposition".into(), proposition),
            ]),
            claim: Some(proposition),
            evidence: result.evidence,
            reasons: evaluated.reasons,
            scope: evaluated.scope,
        })
    }
    fn universal_observe(&mut self, _span: (usize, usize), _stage: usize) -> Result<(), Failure> {
        #[cfg(test)]
        data::observe_actual(_span, self.graph.active, "universal", _stage);
        self.tick(Checkpoint::FiniteIteration)
    }

    fn universal_source(
        &mut self,
        plan: &UniversalPlan,
        template: NodeRef,
        domains: &[NodeRef],
        span: (usize, usize),
        ty: Type,
    ) -> Result<(SourceHandle, Vec<Fact>), Failure> {
        let analyzed = self.environment.universal_source_analysis(
            self.graph,
            span,
            &self.bindings,
            plan,
            domains,
            template,
        )?;
        let analysis = analyzed.analysis;
        self.retained_scope.merge(&analysis.scope);
        let node = Node {
            ty: NodeType::Expression(ty),
            payload: Some(Payload::Expression {
                location: Location::Law { span },
                parameters: analyzed.parameters,
                bindings: self.bindings.clone(),
            }),
            rule: Rule::Input {
                kind: "law",
                location: Location::Law { span },
            },
            arguments: std::iter::once(template)
                .chain(domains.iter().copied())
                .chain(
                    self.environment
                        .source_arguments(self.graph, span, &self.bindings)?,
                )
                .collect(),
            support: vec![],
            evidence: vec![],
            judgment: None,
            scope: analysis.scope.clone(),
            reasons: vec![],
        };
        self.environment.validate(self.graph, &node)?;
        let mut source = None;
        let request = self.request.id.clone();
        let support = analysis.support;
        let registry = &mut self.reasons;
        let retained = &mut self.retained_scope;
        self.graph.push_with_metadata(node, |expression| {
            let missing = analysis.missing.map(|pending| Reason {
                kind: ReasonKind::Missing,
                request,
                dependencies: vec![expression],
                missing: vec![pending.fact],
                location: Some(Location::Law { span }),
            });
            if let Some(reason) = &missing {
                registry.push(reason.clone());
            }
            retained.merge(&analysis.scope);
            source = Some(SourceHandle {
                condition_failed: analysis.condition_failed,
                expression,
                scope: analysis.scope,
                known_value: analysis.known_value,
                missing,
            });
        })?;
        Ok((
            source.ok_or_else(|| Failure::Internal("全域元Sourceのcommitがない".into()))?,
            support,
        ))
    }

    fn universal_finish(
        &mut self,
        source: SourceHandle,
        support: Vec<Fact>,
        ty: Type,
        children: Vec<SymbolicEvaluation>,
        mut comparison: Option<(usize, Evaluated, Evaluated, NodeRef)>,
        local_domain: Option<NodeRef>,
    ) -> Result<SymbolicEvaluation, Failure> {
        let failed = children.iter().any(|a| {
            a.evaluated
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
        });
        if failed {
            comparison = None;
        }
        let expression = source.expression;
        let span = match &self.graph.get(expression)?.payload {
            Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) => *span,
            _ => return Err(Failure::Internal("全域の元出現がない".into())),
        };
        let mut scope = source.scope;
        let mut has_local_domains = local_domain.is_some();
        for child in &children {
            scope.merge(&child.evaluated.scope);
            has_local_domains |= child.has_local_domains;
        }
        let value = source
            .known_value
            .filter(|_| !failed)
            .map(|known| {
                self.value(
                    known,
                    Rule::Input {
                        kind: "law",
                        location: Location::Law { span },
                    },
                    std::iter::once(expression)
                        .chain(local_domain)
                        .chain(children.iter().map(|child| child.evaluated.evaluation))
                        .collect(),
                    support.clone(),
                    scope.clone(),
                )
            })
            .transpose()?;
        let mut reasons = children
            .iter()
            .flat_map(|child| child.evaluated.reasons.iter().cloned())
            .collect::<Vec<_>>();
        if let Some(reason) = source.missing {
            reasons.push(reason);
        }
        sort_reasons(&mut reasons);
        let evaluation = self.push(Node {
            ty: NodeType::Evaluation(ty),
            payload: Some(Payload::Evaluation {
                expression,
                bindings: self.bindings.clone(),
                parts: vec![Part {
                    location: Location::Law { span },
                    value,
                    residual: None,
                    children: children
                        .iter()
                        .map(|child| child.evaluated.evaluation)
                        .collect(),
                }],
                value,
                applicability: "applicable",
            }),
            rule: Rule::Construction("evaluation"),
            arguments: std::iter::once(expression)
                .chain(local_domain)
                .chain(children.iter().map(|child| child.evaluated.evaluation))
                .chain(value)
                .collect(),
            support: support.clone(),
            evidence: vec![],
            judgment: None,
            scope: scope.clone(),
            reasons: reasons.clone(),
        })?;
        Ok(SymbolicEvaluation {
            evaluated: Evaluated {
                expression,
                evaluation,
                value,
                scope,
                support,
                reasons,
                comparison: None,
                residual: None,
            },
            comparison,
            has_local_domains,
        })
    }

    fn universal_pointwise(
        &mut self,
        plan: &UniversalPlan,
        template: NodeRef,
        domains: &[NodeRef],
        id: usize,
    ) -> Result<SymbolicEvaluation, Failure> {
        stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
            self.universal_pointwise_inner(plan, template, domains, id)
        })
    }

    #[inline(never)]
    fn universal_pointwise_inner(
        &mut self,
        plan: &UniversalPlan,
        template: NodeRef,
        domains: &[NodeRef],
        id: usize,
    ) -> Result<SymbolicEvaluation, Failure> {
        self.tick(Checkpoint::Expression)?;
        let expr = self.environment.inputs.law().exprs[id].clone();
        let ty = self
            .environment
            .inputs
            .law()
            .expr_type(id)
            .ok_or_else(|| Failure::Internal("全域元式の型がない".into()))?
            .clone();
        let (source, support) =
            self.universal_source(plan, template, domains, expr.span, ty.clone())?;
        let mut comparison = None;
        let mut local_domain = None;
        let children = match &expr.kind {
            ExprKind::Int(_) | ExprKind::Bool(_) => vec![],
            ExprKind::Dotted(_)
                if data::expression(self.environment.inputs.law(), id, self.control)?.is_some() =>
            {
                vec![]
            }
            ExprKind::Dotted(parts) => {
                let first = parts
                    .first()
                    .ok_or_else(|| Failure::Internal("全域の空Dotted".into()))?;
                if parts.len() == 1 {
                    if let Some((input, _)) = self.environment.pattern_argument(
                        self.graph,
                        first.span,
                        &first.name,
                        &self.bindings,
                    )? {
                        vec![SymbolicEvaluation {
                            evaluated: self.evaluated_reference(input)?,
                            comparison: None,
                            has_local_domains: false,
                        }]
                    } else {
                        self.formal
                            .get(&first.name)
                            .or_else(|| self.lexical.get(&first.name))
                            .cloned()
                            .map(|evaluated| SymbolicEvaluation {
                                evaluated,
                                comparison: None,
                                has_local_domains: false,
                            })
                            .into_iter()
                            .collect()
                    }
                } else if parts.len() == 2 {
                    let owner_ty = self
                        .bindings
                        .iter()
                        .find(|binding| binding.name == first.name)
                        .map(|binding| binding.ty.clone())
                        .or_else(|| {
                            self.formal.get(&first.name).and_then(|value| {
                                match &self.graph.get(value.evaluation).ok()?.ty {
                                    NodeType::Evaluation(ty) => Some(ty.clone()),
                                    _ => None,
                                }
                            })
                        })
                        .ok_or_else(|| self.unsupported(expr.span, "全域式の未確定field owner"))?;
                    let (owner, owner_support) = self.universal_source(
                        plan,
                        template,
                        domains,
                        first.span,
                        owner_ty.clone(),
                    )?;
                    let args = self
                        .formal
                        .get(&first.name)
                        .cloned()
                        .map(|evaluated| SymbolicEvaluation {
                            evaluated,
                            comparison: None,
                            has_local_domains: false,
                        })
                        .into_iter()
                        .collect();
                    vec![self.universal_finish(owner, owner_support, owner_ty, args, None, None)?]
                } else {
                    return Err(self.unsupported(expr.span, "全域式の複数fieldドット列"));
                }
            }
            ExprKind::Field { base, .. }
            | ExprKind::Group(base)
            | ExprKind::Unary { operand: base, .. } => {
                let child = self.universal_pointwise(plan, template, domains, *base)?;
                if matches!(expr.kind, ExprKind::Group(_)) {
                    comparison = child.comparison.clone();
                }
                vec![child]
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let left = self.universal_pointwise(plan, template, domains, *lhs)?;
                let right = self.universal_pointwise(plan, template, domains, *rhs)?;
                if *op == BinOp::Eq {
                    comparison = Some((
                        id,
                        left.evaluated.clone(),
                        right.evaluated.clone(),
                        source.expression,
                    ));
                }
                vec![left, right]
            }
            ExprKind::Match { scrutinee, arms } => {
                let input = self.universal_pointwise(plan, template, domains, *scrutinee)?;
                let selected = data::select(
                    self.environment.inputs.law(),
                    id,
                    input
                        .evaluated
                        .value
                        .map(|value| self.graph.scalar(value))
                        .transpose()?,
                    self.control,
                )?;
                let mut children = vec![input];
                if let Some(arm) = selected {
                    #[cfg(test)]
                    data::observe_actual(expr.span, self.graph.active, "universal_match", arm);
                    self.tick(Checkpoint::FiniteIteration)?;
                    let body = self.universal_pointwise(plan, template, domains, arms[arm].body)?;
                    comparison = body.comparison.clone();
                    children.push(body);
                }
                children
            }
            ExprKind::Let {
                name: binder,
                value,
                body,
            } => {
                let value = self.universal_pointwise(plan, template, domains, *value)?;
                let old = self
                    .lexical
                    .insert(binder.name.clone(), value.evaluated.clone());
                let body_result = self.universal_pointwise(plan, template, domains, *body);
                if let Some(old) = old {
                    self.lexical.insert(binder.name.clone(), old);
                } else {
                    self.lexical.remove(&binder.name);
                }
                let body = body_result?;
                comparison = body.comparison.clone();
                vec![value, body]
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond = self.universal_pointwise(plan, template, domains, *cond)?;
                let left = self.universal_pointwise(plan, template, domains, *then_branch)?;
                let right = self.universal_pointwise(plan, template, domains, *else_branch)?;
                comparison = match cond
                    .evaluated
                    .value
                    .map(|value| self.graph.scalar(value))
                    .transpose()?
                {
                    Some(Scalar::Bool(true)) => left.comparison.clone(),
                    Some(Scalar::Bool(false)) => right.comparison.clone(),
                    _ => None,
                };
                vec![cond, left, right]
            }
            ExprKind::Quant { split, .. } => {
                let crate::law::ast::QuantSplit::Fixed {
                    domain: crate::law::ast::QuantDomain::Type(_),
                    body,
                } = split
                else {
                    return Err(self.unsupported(expr.span, "全域アフィン式内の未対応量化"));
                };
                let mut nested_domains = domains.to_vec();
                if let Some(parameter) = self
                    .environment
                    .universal_local_parameter(self.graph, plan, template, domains, id)?
                {
                    let domain = self.push(Node {
                        ty: NodeType::Domain,
                        payload: Some(Payload::TypeDomain {
                            ty: parameter.kind.ty(),
                        }),
                        rule: Rule::Input {
                            kind: "law",
                            location: Location::Law {
                                span: parameter.binder,
                            },
                        },
                        arguments: vec![source.expression],
                        support: vec![],
                        evidence: vec![],
                        judgment: None,
                        scope: source.scope.clone(),
                        reasons: vec![],
                    })?;
                    local_domain = Some(domain);
                    nested_domains.push(domain);
                    #[cfg(test)]
                    data::observe_actual(expr.span, self.graph.active, "universal_local", 1);
                    self.tick(Checkpoint::FiniteIteration)?;
                }
                let body = self.universal_pointwise(plan, template, &nested_domains, *body)?;
                if local_domain.is_none()
                    || self.environment.universal_local_retains_comparison(
                        self.graph,
                        plan,
                        template,
                        &nested_domains,
                        id,
                        &self.bindings,
                    )?
                {
                    comparison = body.comparison.clone();
                }
                vec![body]
            }
            ExprKind::Call { args, .. } if self.environment.named_view(id)?.is_some() => {
                let declaration = self
                    .environment
                    .named_view(id)?
                    .ok_or_else(|| Failure::Internal("全域call targetがない".into()))?;
                let Signature::View { params, body, .. } = &declaration.signature else {
                    unreachable!()
                };
                let mut arguments = Vec::new();
                for argument in args {
                    arguments.push(self.universal_pointwise(plan, template, domains, *argument)?);
                }
                let owned = self.environment.owns_call(id)?;
                let values = if owned {
                    arguments
                        .iter()
                        .map(|a| {
                            a.evaluated
                                .value
                                .map(|r| self.graph.scalar(r).cloned())
                                .transpose()
                        })
                        .collect::<Result<Vec<_>, _>>()?
                } else {
                    vec![]
                };
                let checks = if arguments.iter().any(|a| {
                    a.evaluated
                        .reasons
                        .iter()
                        .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
                }) {
                    super::super::environment::owned_call::Checks {
                        blocked: true,
                        ..Default::default()
                    }
                } else {
                    self.environment
                        .owned_call_checks(declaration, &values, None, expr.span)?
                };
                if checks.failure.is_some() || checks.blocked {
                    let has_local_domains = arguments.iter().any(|a| a.has_local_domains);
                    let evaluated = self.owned_call_finish_at(
                        source,
                        expr.span,
                        ty,
                        arguments.into_iter().map(|a| a.evaluated).collect(),
                        None,
                        checks,
                    )?;
                    return Ok(SymbolicEvaluation {
                        evaluated,
                        comparison: None,
                        has_local_domains,
                    });
                }
                let caller = self.graph.active;
                let frame = self.graph.frames.len();
                self.graph.frames.push(super::super::call::Frame {
                    caller,
                    source: source.expression,
                    arguments: arguments
                        .iter()
                        .map(|argument| argument.evaluated.evaluation)
                        .collect(),
                });
                self.graph.active = super::super::call::Context {
                    frame: Some(frame),
                    iteration: None,
                    ..caller
                };
                let old_bindings = std::mem::take(&mut self.bindings);
                let old_formal = std::mem::take(&mut self.formal);
                let old_lexical = std::mem::take(&mut self.lexical);
                for (param, argument) in params.iter().zip(&arguments) {
                    self.formal
                        .insert(param.name.clone(), argument.evaluated.clone());
                    if let Some(value) = argument.evaluated.value {
                        self.bindings.push(Binding {
                            name: param.name.clone(),
                            ty: param.ty.erase(),
                            value,
                        });
                    }
                }
                let body_result = self.universal_pointwise(plan, template, domains, *body);
                self.graph.active = caller;
                self.bindings = old_bindings;
                self.formal = old_formal;
                self.lexical = old_lexical;
                let body = body_result?;
                let known = body
                    .evaluated
                    .value
                    .map(|r| self.graph.scalar(r))
                    .transpose()?;
                let checks = self.environment.owned_call_checks(
                    declaration,
                    &values,
                    Some(known),
                    expr.span,
                )?;
                if checks.failure.is_some() || checks.blocked {
                    arguments.push(body);
                    let has_local_domains = arguments.iter().any(|a| a.has_local_domains);
                    let evaluated = self.owned_call_finish_at(
                        source,
                        expr.span,
                        ty,
                        arguments.into_iter().map(|a| a.evaluated).collect(),
                        None,
                        checks,
                    )?;
                    return Ok(SymbolicEvaluation {
                        evaluated,
                        comparison: None,
                        has_local_domains,
                    });
                }
                comparison = body.comparison.clone();
                arguments.push(body);
                arguments
            }
            ExprKind::Fn { .. }
            | ExprKind::Tuple(_)
            | ExprKind::ListLit { .. }
            | ExprKind::SetLit { .. }
            | ExprKind::None(_)
            | ExprKind::Some(_)
            | ExprKind::Unit
            | ExprKind::Str(_)
            | ExprKind::Index { .. }
            | ExprKind::Call { .. } => {
                let children = self
                    .environment
                    .composite_children(id)?
                    .ok_or_else(|| self.unsupported(expr.span, "全域式の未対応構成"))?;
                let mut evaluated = Vec::new();
                for child in children {
                    evaluated.push(self.universal_pointwise(plan, template, domains, child)?);
                }
                evaluated
            }
            _ => return Err(self.unsupported(expr.span, "全域アフィン式の未対応構成")),
        };
        let result =
            self.universal_finish(source, support, ty, children, comparison, local_domain)?;
        self.tick(Checkpoint::Expression)?;
        Ok(result)
    }
}
