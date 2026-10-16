//! 元のbinderと実producerを保つ、Z/Qの全称アフィン等値。
use super::*;
use crate::law::{
    ast::{QuantDomain, QuantKind, QuantSplit},
    model::Signature,
};
use crate::observed::affine::{self, NumberType, Parameter};
#[path = "universal_validation.rs"]
pub(super) mod validation;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct UniversalPlan {
    pub template_span: (usize, usize),
    pub body: usize,
    pub guard: Option<usize>,
    pub parameters: Vec<Parameter>,
    pub family: bool,
}
#[derive(Clone)]
pub(super) struct AnalysisContext {
    pub plan: UniversalPlan,
    pub template: Option<NodeRef>,
    pub domains: Vec<NodeRef>,
    pub completions: Vec<(Fact, Scalar)>,
}
pub(in crate::observed) struct UniversalSourceAnalysis {
    pub parameters: Vec<(String, Type)>,
    pub analysis: SourceAnalysis,
}
pub(in crate::observed) struct UniversalAnalysis {
    pub analysis: SourceAnalysis,
    pub classification: Option<affine::Universal>,
    pub comparison: Option<(usize, usize)>,
    pub comparison_expression: Option<usize>,
    pub value: Option<bool>,
    pub guard_value: Option<bool>,
}
type CounterexampleBinding = (String, Type, Scalar, (usize, usize));
fn number(ty: &Type) -> Option<NumberType> {
    match ty {
        Type::Z => Some(NumberType::Z),
        Type::Q => Some(NumberType::Q),
        _ => None,
    }
}
impl Environment<'_> {
    pub(super) fn universal_completion_frame(
        &self,
        graph: &Graph,
        index: usize,
    ) -> Result<Option<FrameInputs>, ValidationFailure> {
        let active = self.universal_context.borrow().clone();
        let Some(mut original) = active.filter(|context| !context.completions.is_empty()) else {
            return Ok(None);
        };
        original.completions.clear();
        // まず提示された元実引数を、補完を入れずに照合する。代入した値を元の
        // unknown Evaluationの値と取り違えず、その後に原ASTを補完下で再分析する。
        let (bindings, mut variables, base) =
            self.with_universal(original, || self.frame_arguments(graph, index))?;
        let frame = graph.frames.get(index).ok_or("全域補完の元frameがない")?;
        let call = *self
            .expressions
            .get(&self.expression_span(graph, frame.source)?)
            .ok_or("全域補完の元callがない")?;
        let declaration = self.named_view(call)?.ok_or("全域補完の元viewがない")?;
        let Signature::View { params, .. } = &declaration.signature else {
            unreachable!()
        };
        let ExprKind::Call { args, .. } = &self.inputs.law().exprs[call].kind else {
            unreachable!()
        };
        let previous = self.context.replace(Some(frame.caller));
        let result = (|| {
            for ((parameter, arg), reference) in params.iter().zip(args).zip(&frame.arguments) {
                self.tick()?;
                let (_, actual, _) = self.evaluation(graph, *reference)?;
                let analysis =
                    self.analyze_source(graph, self.inputs.law().exprs[*arg].span, actual)?;
                let mut scope = analysis.scope;
                scope.merge(&base);
                variables.insert(
                    parameter.name.clone(),
                    SourceValue {
                        comparison: analysis.comparison,
                        affine: analysis.affine,
                        scope,
                        known_value: analysis.known_value,
                        support: analysis.support,
                        scalar_scope: analysis.scalar_scope,
                    },
                );
            }
            Ok(Some((bindings, variables, base)))
        })();
        self.context.set(previous);
        result
    }
    fn universal_completions(&self, template: NodeRef) -> Vec<(Fact, Scalar)> {
        self.universal_context
            .borrow()
            .as_ref()
            .filter(|context| context.template == Some(template))
            .map(|context| context.completions.clone())
            .unwrap_or_default()
    }
    pub(super) fn universal_missing_value(
        &self,
        fact: &Fact,
        ty: &Type,
    ) -> Result<Option<Scalar>, ValidationFailure> {
        self.tick()?;
        let context = self.universal_context.borrow();
        let Some((_, value)) = context.as_ref().and_then(|context| {
            context
                .completions
                .iter()
                .find(|(candidate, _)| candidate == fact)
        }) else {
            return Ok(None);
        };
        if number(ty).is_none() || value.ty() != *ty {
            return Err("全域数値補完の元slot型が違う".into());
        }
        Ok(Some(value.clone()))
    }
    pub(in crate::observed) fn universal_completion_analysis(
        &self,
        graph: &Graph,
        template: NodeRef,
        domains: &[NodeRef],
        values: &[(Fact, Scalar)],
    ) -> Result<UniversalAnalysis, ValidationFailure> {
        let fixed = self.expression_bindings(graph, self.universal_raw_body(graph, template)?)?;
        let plan = self.universal_plan_at(graph, template, fixed)?;
        self.universal_check_domains(graph, template, domains, &plan)?;
        for (index, (fact, value)) in values.iter().enumerate() {
            self.tick()?;
            self.fact(fact)?;
            if fact.atom.is_some() || values[..index].iter().any(|(previous, _)| previous == fact) {
                return Err("全域補完Factが観測済み・重複である".into());
            }
            let field = self.field(
                &fact.snapshot,
                &fact.subject,
                fact.field.as_deref().ok_or("全域数値補完にfieldがない")?,
            )?;
            if !matches!(field.slot, Slot::Missing)
                || number(&field.ty).is_none()
                || value.ty() != field.ty
            {
                return Err("全域数値補完の元欠測slot・型が違う".into());
            }
        }
        self.with_universal(
            AnalysisContext {
                plan,
                template: Some(template),
                domains: domains.to_vec(),
                completions: values.to_vec(),
            },
            || self.universal_analysis(graph, template, domains, fixed),
        )
    }
    pub(in crate::observed) fn universal_raw_body(
        &self,
        graph: &Graph,
        template: NodeRef,
    ) -> Result<NodeRef, ValidationFailure> {
        match &graph.get(template)?.payload {
            Some(Payload::Expression { .. }) => Ok(template),
            Some(Payload::ParameterizedTransform {
                operation: TransformOp::Not,
                operands,
                bindings,
                parameters,
            }) if operands.len() == 1 => {
                let conjunction = graph.get(operands[0])?;
                let Some(Payload::ParameterizedTransform {
                    operation: TransformOp::And,
                    operands: and,
                    bindings: and_bindings,
                    parameters: and_parameters,
                }) = &conjunction.payload
                else {
                    return Err("全域適用の含意and式がない".into());
                };
                if and.len() != 2 || and_bindings != bindings || and_parameters != parameters {
                    return Err("全域適用の含意束縛・軸が違う".into());
                }
                let negation = graph.get(and[1])?;
                let Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Not,
                    operands: body,
                    bindings: body_bindings,
                    parameters: body_parameters,
                }) = &negation.payload
                else {
                    return Err("全域適用の元body否定式がない".into());
                };
                if body.len() != 1 || body_bindings != bindings || body_parameters != parameters {
                    return Err("全域適用の元body束縛・軸が違う".into());
                }
                Ok(body[0])
            }
            _ => Err("全域templateが元Source/固定含意式でない".into()),
        }
    }
    pub(super) fn universal_quantifier_source_value(
        &self,
        id: usize,
        variables: &BTreeMap<String, SourceValue>,
        base: &Scope,
        reading: &str,
    ) -> Result<Option<SourceValue>, ValidationFailure> {
        let ExprKind::Quant {
            kind: QuantKind::Forall,
            var,
            split:
                QuantSplit::Fixed {
                    domain: QuantDomain::Type(_),
                    body,
                },
        } = &self.inputs.law().exprs[id].kind
        else {
            return Ok(None);
        };
        let ty = self.inputs.law().quantifier_types[id]
            .as_ref()
            .ok_or("全域binder型がない")?;
        if number(ty).is_none() {
            return Ok(None);
        }
        if self.universal_context.borrow().is_none() {
            let context = self
                .scoped_context
                .get()
                .or(self.context.get())
                .unwrap_or_default();
            let mut plan = UniversalPlan {
                template_span: self.inputs.law().exprs[id].span,
                body: id,
                guard: None,
                parameters: Vec::new(),
                family: false,
            };
            self.universal_strip_at(context, &mut plan)?;
            return self.with_universal(
                AnalysisContext {
                    plan: plan.clone(),
                    template: None,
                    domains: Vec::new(),
                    completions: Vec::new(),
                },
                || {
                    let mut scope = base.clone();
                    self.universal_extend_scope(&mut scope)?;
                    let mut local = self.copy_variables(variables)?;
                    for parameter in &plan.parameters {
                        local.insert(
                            parameter.name.clone(),
                            self.universal_parameter_value(
                                parameter.binder,
                                &parameter.name,
                                &parameter.kind.ty(),
                                &scope,
                            )?,
                        );
                    }
                    let mut value = self.scoped_ast(plan.body, &local, &scope, reading)?;
                    // 全称軸は、bodyでその変数を使用しない場合も元量化に属する。
                    value.scope.merge(&scope);
                    value.known_value = match value.comparison.as_ref() {
                        Some(predicate) if predicate.op == BinOp::Eq => affine::universal_equality(
                            Some(&predicate.left),
                            Some(&predicate.right),
                            &plan.parameters,
                            &self.control,
                        )?
                        .and_then(|classification| classification.value)
                        .map(Scalar::Bool),
                        _ => value.known_value,
                    };
                    value.affine = None;
                    value.comparison = None;
                    value.scalar_scope = value.known_value.as_ref().map(|_| value.scope.clone());
                    Ok(Some(value))
                },
            );
        }
        let mut local = self.copy_variables(variables)?;
        local.insert(
            var.name.clone(),
            self.universal_parameter_value(var.span, &var.name, ty, base)?,
        );
        let mut value = self.scoped_ast(*body, &local, base, reading)?;
        value.scalar_scope = value.known_value.as_ref().map(|_| value.scope.clone());
        value.affine = None;
        value.comparison = None;
        Ok(Some(value))
    }
    pub(super) fn universal_parameter_value(
        &self,
        binder: (usize, usize),
        name: &str,
        ty: &Type,
        base: &Scope,
    ) -> Result<SourceValue, ValidationFailure> {
        let active = self.universal_context.borrow();
        let context = active
            .as_ref()
            .ok_or_else(|| ValidationFailure::UnsupportedExpression {
                location: Location::Law { span: binder },
                feature: "Z/Q全域parameterの記号分析".into(),
            })?;
        let parameter = context
            .plan
            .parameters
            .iter()
            .find(|parameter| {
                parameter.binder == binder && parameter.name == name && parameter.kind.ty() == *ty
            })
            .ok_or_else(|| ValidationFailure::UnsupportedExpression {
                location: Location::Law { span: binder },
                feature: "call展開内で追加されるZ/Q全称binderの全域Plan".into(),
            })?;
        Ok(SourceValue {
            comparison: None,
            affine: affine::parameter(ty, parameter, &self.control)?.map(Box::new),
            scope: base.clone(),
            known_value: None,
            support: Vec::new(),
            scalar_scope: None,
        })
    }
    pub(super) fn universal_extend_scope(
        &self,
        scope: &mut Scope,
    ) -> Result<(), ValidationFailure> {
        if let Some(context) = self.universal_context.borrow().as_ref() {
            scope.assignments = true;
            for (index, parameter) in context.plan.parameters.iter().enumerate() {
                self.tick()?;
                scope.add_quantifier(Quantifier {
                    kind: QuantKind::Forall,
                    name: parameter.name.clone(),
                    ty: parameter.kind.ty(),
                    domain: context.domains.get(index).copied(),
                    occurrence: parameter.binder,
                    context: Some(parameter.context),
                });
            }
        }
        Ok(())
    }
    pub(in crate::observed) fn universal_family_plan(
        &self,
        graph: &Graph,
        request: &Request,
        bindings: &[Binding],
    ) -> Result<Option<UniversalPlan>, ValidationFailure> {
        if request.kind != QuestionKind::Check {
            return Ok(None);
        }
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration())
            .ok_or("全域の元Lawがない")?;
        let Signature::Law {
            params,
            guard,
            body,
            ..
        } = &declaration.signature
        else {
            return Ok(None);
        };
        let mut parameters = Vec::new();
        let context = self.current_context(graph);
        for param in params {
            self.tick()?;
            if bindings.iter().any(|binding| binding.name == param.name) {
                continue;
            }
            let Some(kind) = number(&param.ty) else {
                return Ok(None);
            };
            parameters.push(Parameter {
                binder: param.span,
                name: param.name.clone(),
                context,
                kind,
            });
        }
        if parameters.is_empty() {
            return Ok(None);
        }
        let mut plan = UniversalPlan {
            template_span: self.inputs.law().exprs[*body].span,
            body: *body,
            guard: *guard,
            parameters,
            family: true,
        };
        self.universal_strip_quantifiers(graph, &mut plan)?;
        Ok(Some(plan))
    }
    pub(in crate::observed) fn universal_quantifier_plan(
        &self,
        graph: &Graph,
        id: usize,
        _bindings: &[Binding],
    ) -> Result<Option<UniversalPlan>, ValidationFailure> {
        let mut plan = UniversalPlan {
            template_span: self.inputs.law().exprs[id].span,
            body: id,
            guard: None,
            parameters: Vec::new(),
            family: false,
        };
        self.universal_strip_quantifiers(graph, &mut plan)?;
        if let Some(request) = graph.requests.get(self.current_context(graph).request)
            && request.kind == QuestionKind::Check
            && let Some(declaration) = self.inputs.law().declarations.get(request.declaration())
            && let Signature::Law { body, guard, .. } = &declaration.signature
            && *body == id
        {
            plan.guard = *guard;
        }
        Ok((!plan.parameters.is_empty()).then_some(plan))
    }
    fn universal_strip_quantifiers(
        &self,
        graph: &Graph,
        plan: &mut UniversalPlan,
    ) -> Result<(), ValidationFailure> {
        self.universal_strip_at(self.current_context(graph), plan)
    }
    fn universal_strip_at(
        &self,
        context: crate::observed::call::Context,
        plan: &mut UniversalPlan,
    ) -> Result<(), ValidationFailure> {
        loop {
            self.tick()?;
            let expression = &self.inputs.law().exprs[plan.body];
            let ExprKind::Quant {
                kind: QuantKind::Forall,
                var,
                split:
                    QuantSplit::Fixed {
                        domain: QuantDomain::Type(_),
                        body,
                    },
            } = &expression.kind
            else {
                break;
            };
            let ty = self
                .inputs
                .law()
                .quantifier_types
                .get(plan.body)
                .and_then(Option::as_ref)
                .ok_or("全域binderの元型がない")?;
            let Some(kind) = number(ty) else {
                break;
            };
            plan.parameters.push(Parameter {
                binder: var.span,
                name: var.name.clone(),
                context,
                kind,
            });
            plan.body = *body;
        }
        Ok(())
    }
    fn with_universal<T>(
        &self,
        context: AnalysisContext,
        run: impl FnOnce() -> Result<T, ValidationFailure>,
    ) -> Result<T, ValidationFailure> {
        self.validation_session(|| {
            let old = self.universal_context.replace(Some(context));
            let result = run();
            self.universal_context.replace(old);
            result
        })
    }
    pub(in crate::observed) fn universal_template_source_analysis(
        &self,
        graph: &Graph,
        plan: &UniversalPlan,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<UniversalSourceAnalysis, ValidationFailure> {
        self.with_universal(
            AnalysisContext {
                plan: plan.clone(),
                template: None,
                domains: Vec::new(),
                completions: Vec::new(),
            },
            || self.universal_analyze_at(graph, span, bindings),
        )
    }
    pub(in crate::observed) fn universal_source_analysis(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
        plan: &UniversalPlan,
        domains: &[NodeRef],
        template: NodeRef,
    ) -> Result<UniversalSourceAnalysis, ValidationFailure> {
        self.universal_check_domains(graph, template, domains, plan)?;
        self.with_universal(
            AnalysisContext {
                plan: plan.clone(),
                template: Some(template),
                domains: domains.to_vec(),
                completions: self.universal_completions(template),
            },
            || self.universal_analyze_at(graph, span, bindings),
        )
    }
    fn universal_analyze_at(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<UniversalSourceAnalysis, ValidationFailure> {
        self.tick()?;
        let analysis = self.universal_uncached_source(graph, span, bindings)?;
        let mut parameters = Vec::new();
        let law = self.inputs.law();
        let declaration = law
            .declarations
            .values()
            .find(|declaration| declaration.span.0 <= span.0 && span.1 <= declaration.span.1)
            .ok_or("全域Sourceの元宣言がない")?;
        let declared = match &declaration.signature {
            Signature::Law { params, .. } | Signature::View { params, .. } => params,
            _ => return Err("全域Sourceの元宣言型が違う".into()),
        };
        for parameter in declared {
            self.tick()?;
            if number(&parameter.ty).is_some()
                && !bindings
                    .iter()
                    .any(|binding| binding.name == parameter.name)
            {
                parameters.push((parameter.name.clone(), parameter.ty.erase()));
            }
        }
        let mut lexical = self
            .lexical_context(span)?
            .into_iter()
            .filter_map(|(name, origin)| match origin {
                LexicalOrigin::Universal(id) => Some((id, name)),
                _ => None,
            })
            .collect::<Vec<_>>();
        lexical.sort_by_key(|(id, _)| law.exprs[*id].span.0);
        for (id, name) in lexical {
            let ty = law.quantifier_types[id]
                .as_ref()
                .ok_or("自由全域binder型がない")?;
            parameters.push((name, ty.clone()));
        }
        Ok(UniversalSourceAnalysis {
            parameters,
            analysis,
        })
    }
    pub(super) fn universal_uncached_source(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<SourceAnalysis, ValidationFailure> {
        let context = self.current_context(graph);
        let previous = self.scoped_context.replace(Some(context));
        let previous_completion = self.completion_values.replace(Vec::new());
        let result = (|| {
            if let Some(case) = context.case {
                *self.completion_values.borrow_mut() = self.completion_values(graph, case)?;
            }
            self.analyze_source_uncached(graph, span, bindings)
        })();
        self.completion_values.replace(previous_completion);
        self.scoped_context.set(previous);
        result
    }
    pub(in crate::observed) fn universal_analysis(
        &self,
        graph: &Graph,
        template: NodeRef,
        domains: &[NodeRef],
        bindings: &[Binding],
    ) -> Result<UniversalAnalysis, ValidationFailure> {
        // 数値補完証拠の再検査から再入するため、分析用の局所値を持つ
        // フレームを確保する前に、共通sessionと同じ保護を適用する。
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.universal_analysis_inner(graph, template, domains, bindings)
        })
    }
    fn universal_analysis_inner(
        &self,
        graph: &Graph,
        template: NodeRef,
        domains: &[NodeRef],
        bindings: &[Binding],
    ) -> Result<UniversalAnalysis, ValidationFailure> {
        let previous = self.context.replace(Some(graph.context_at(template.0)));
        let result = (|| {
            let plan = self.universal_plan_at(graph, template, bindings)?;
            self.universal_check_domains(graph, template, domains, &plan)?;
            self.with_universal(
                AnalysisContext {
                    plan: plan.clone(),
                    template: Some(template),
                    domains: domains.to_vec(),
                    completions: self.universal_completions(template),
                },
                || {
                    let guard_analysis = plan
                        .guard
                        .map(|guard| {
                            self.universal_uncached_source(
                                graph,
                                self.inputs.law().exprs[guard].span,
                                bindings,
                            )
                        })
                        .transpose()?;
                    let guard_value = match guard_analysis
                        .as_ref()
                        .and_then(|guard| guard.known_value.as_ref())
                    {
                        Some(Scalar::Bool(value)) => Some(*value),
                        None => None,
                        _ => return Err("全域guardの型がBoolでない".into()),
                    };
                    if guard_value == Some(false) {
                        let mut analysis = guard_analysis.clone().ok_or("全域guard分析がない")?;
                        analysis.scope.merge(&graph.get(template)?.scope);
                        analysis.known_value = Some(Scalar::Bool(true));
                        analysis.scalar_scope = Some(analysis.scope.clone());
                        return Ok(UniversalAnalysis {
                            analysis,
                            classification: None,
                            comparison: None,
                            comparison_expression: None,
                            value: Some(true),
                            guard_value,
                        });
                    }
                    let mut analysis = self.universal_uncached_source(
                        graph,
                        self.inputs.law().exprs[plan.body].span,
                        bindings,
                    )?;
                    let predicate = analysis.comparison.as_ref();
                    let classification = match predicate {
                        Some(predicate) if predicate.op == BinOp::Eq => affine::universal_equality(
                            Some(&predicate.left),
                            Some(&predicate.right),
                            &plan.parameters,
                            &self.control,
                        )?,
                        _ => None,
                    };
                    let comparison_expression = predicate.map(|predicate| predicate.expression);
                    let comparison = comparison_expression.and_then(|id| {
                        match self.inputs.law().exprs[id].kind {
                            ExprKind::Binary { lhs, rhs, .. } => Some((lhs, rhs)),
                            _ => None,
                        }
                    });
                    let body_value = classification
                        .as_ref()
                        .and_then(|classification| classification.value)
                        .or(match analysis.known_value.as_ref() {
                            Some(Scalar::Bool(value)) => Some(*value),
                            _ => None,
                        });
                    let value = if plan.guard.is_some() {
                        conditional_bool(guard_value, body_value)
                    } else {
                        body_value
                    };
                    if let Some(guard) = &guard_analysis {
                        analysis.scope.merge(&guard.scope);
                        analysis.support.extend(guard.support.iter().cloned());
                        analysis.support.sort();
                        analysis.support.dedup();
                    }
                    analysis.known_value = value.map(Scalar::Bool);
                    analysis.scalar_scope = value.map(|_| analysis.scope.clone());
                    Ok(UniversalAnalysis {
                        analysis,
                        classification,
                        comparison,
                        comparison_expression,
                        value,
                        guard_value,
                    })
                },
            )
        })();
        self.context.set(previous);
        result
    }
    pub(in crate::observed) fn universal_substitution_analysis(
        &self,
        graph: &Graph,
        original: NodeRef,
        bindings: &[Binding],
        template: NodeRef,
        domains: &[NodeRef],
    ) -> Result<UniversalSourceAnalysis, ValidationFailure> {
        let fixed = self.expression_bindings(graph, self.universal_raw_body(graph, template)?)?;
        let plan = self.universal_plan_at(graph, template, fixed)?;
        let classification = self
            .universal_analysis(graph, template, domains, fixed)?
            .classification
            .ok_or("全域代入に元アフィン等式の分析がない")?;
        let assignment = classification
            .common_counterexample
            .as_ref()
            .ok_or("全域代入に全補完共通のparameter反例がない")?;
        let original_bindings = self.expression_bindings(graph, original)?;
        let expected_bindings =
            self.universal_counterexample_bindings(graph, original, template, domains)?;
        let Some(Payload::Expression {
            parameters: free, ..
        }) = &graph.get(original)?.payload
        else {
            return Err("全域代入の元Sourceでない".into());
        };
        for binding in original_bindings {
            if !bindings.contains(binding) {
                return Err("全域代入が元固定束縛を変更した".into());
            }
        }
        let span = self.expression_span(graph, original)?;
        let old_context = self.context.replace(Some(graph.context_at(original.0)));
        let result = self.with_universal(
            AnalysisContext {
                plan: plan.clone(),
                template: Some(template),
                domains: domains.to_vec(),
                completions: Vec::new(),
            },
            || {
                let mut result = self.universal_analyze_at(graph, span, original_bindings)?;
                for binding in bindings
                    .iter()
                    .filter(|binding| !original_bindings.contains(binding))
                {
                    self.tick()?;
                    if !free
                        .iter()
                        .any(|(name, ty)| name == &binding.name && ty == &binding.ty)
                    {
                        return Err("全域代入が元自由parameter型と違う".into());
                    }
                    let expected = expected_bindings
                        .iter()
                        .find(|(name, ty, _, _)| name == &binding.name && ty == &binding.ty)
                        .ok_or("全域代入に元自由parameterがない")?;
                    if graph.scalar(binding.value)? != &expected.2 {
                        return Err("全域代入のparameter値が元全域反例と違う".into());
                    }
                }
                if let Some(form) = &result.analysis.affine {
                    let form = affine::substitute_parameters(form, assignment, &self.control)?;
                    result.analysis.known_value = form.value(&self.control)?;
                    result.analysis.affine = Some(Box::new(form));
                }
                if let Some(predicate) = &result.analysis.comparison {
                    let left =
                        affine::substitute_parameters(&predicate.left, assignment, &self.control)?;
                    let right =
                        affine::substitute_parameters(&predicate.right, assignment, &self.control)?;
                    result.analysis.known_value =
                        affine::equality(predicate.op, Some(&left), Some(&right), &self.control)?
                            .map(|(value, _)| value);
                    if result.analysis.known_value.is_none() && predicate.op == BinOp::Eq {
                        result.analysis.known_value = affine::universal_equality(
                            Some(&left),
                            Some(&right),
                            &[],
                            &self.control,
                        )?
                        .and_then(|classification| classification.value)
                        .map(Scalar::Bool);
                    }
                    result.analysis.comparison = Some(Box::new(AffinePredicate {
                        expression: predicate.expression,
                        op: predicate.op,
                        left,
                        right,
                    }));
                }
                result.analysis.scalar_scope = result
                    .analysis
                    .known_value
                    .as_ref()
                    .map(|_| result.analysis.scope.clone());
                result
                    .parameters
                    .retain(|(name, _)| !bindings.iter().any(|binding| binding.name == *name));
                Ok(result)
            },
        );
        self.context.set(old_context);
        result
    }
    pub(in crate::observed) fn universal_counterexample_bindings(
        &self,
        graph: &Graph,
        original: NodeRef,
        template: NodeRef,
        domains: &[NodeRef],
    ) -> Result<Vec<CounterexampleBinding>, ValidationFailure> {
        let fixed = self.expression_bindings(graph, self.universal_raw_body(graph, template)?)?;
        let plan = self.universal_plan_at(graph, template, fixed)?;
        let classified = self
            .universal_analysis(graph, template, domains, fixed)?
            .classification
            .ok_or("具体全域反例の元分析がない")?;
        let assignment = classified
            .common_counterexample
            .as_ref()
            .ok_or("全補完共通の具体反例がない")?;
        let Some(Payload::Expression {
            parameters: free, ..
        }) = &graph.get(original)?.payload
        else {
            return Err("具体全域反例の元Sourceがない".into());
        };
        let span = self.expression_span(graph, original)?;
        let declaration = self
            .inputs
            .law()
            .declarations
            .values()
            .find(|declaration| declaration.span.0 <= span.0 && span.1 <= declaration.span.1)
            .ok_or("具体反例の元宣言がない")?;
        let formal = match &declaration.signature {
            Signature::Law { params, .. } | Signature::View { params, .. } => params,
            _ => return Err("具体反例の元署名が違う".into()),
        };
        let previous = self.context.replace(Some(graph.context_at(original.0)));
        let result = self.with_universal(
            AnalysisContext {
                plan: plan.clone(),
                template: Some(template),
                domains: domains.to_vec(),
                completions: Vec::new(),
            },
            || {
                let variables = graph
                    .context_at(original.0)
                    .frame
                    .map(|frame| {
                        self.frame_arguments(graph, frame)
                            .map(|(_, variables, _)| variables)
                    })
                    .transpose()?;
                let mut result = Vec::new();
                for (name, ty) in free {
                    self.tick()?;
                    let (value, binder) = if let Some(value) =
                        variables.as_ref().and_then(|variables| variables.get(name))
                    {
                        let form = value
                            .affine
                            .as_deref()
                            .ok_or("具体反例の実formalがアフィンでない")?;
                        let Some(scalar) =
                            affine::substitute_parameters(form, assignment, &self.control)?
                                .value(&self.control)?
                        else {
                            // callerの全称parameterを具体化しても、実引数の
                            // Missingは残り得る。formalを架空のScalarで埋めない。
                            continue;
                        };
                        (
                            scalar,
                            formal
                                .iter()
                                .find(|parameter| parameter.name == *name)
                                .ok_or("具体反例の元formalがない")?
                                .span,
                        )
                    } else {
                        let (parameter, value) = assignment
                            .iter()
                            .find(|(parameter, _)| {
                                parameter.name == *name && parameter.kind.ty() == *ty
                            })
                            .ok_or("具体反例の元parameterがない")?;
                        (value.clone(), parameter.binder)
                    };
                    result.push((name.clone(), ty.clone(), value, binder));
                }
                Ok(result)
            },
        );
        self.context.set(previous);
        result
    }
    fn universal_plan_at(
        &self,
        graph: &Graph,
        template: NodeRef,
        bindings: &[Binding],
    ) -> Result<UniversalPlan, ValidationFailure> {
        let previous = self.context.replace(Some(graph.context_at(template.0)));
        let result = (|| {
            let raw = self.universal_raw_body(graph, template)?;
            let span = self.expression_span(graph, raw)?;
            let id = *self
                .expressions
                .get(&span)
                .ok_or("全域templateの元ASTがない")?;
            let request = graph
                .requests
                .get(self.current_context(graph).request)
                .ok_or("全域templateの元Requestがない")?;
            let plan = self
                .universal_family_plan(graph, request, bindings)?
                .filter(|plan| plan.template_span == span)
                .or(self.universal_quantifier_plan(graph, id, bindings)?);
            plan.ok_or_else(|| "全域templateに元全称binderがない".into())
        })();
        self.context.set(previous);
        result
    }
    fn universal_check_domains(
        &self,
        graph: &Graph,
        template: NodeRef,
        domains: &[NodeRef],
        plan: &UniversalPlan,
    ) -> Result<(), ValidationFailure> {
        if self.expression_span(graph, self.universal_raw_body(graph, template)?)?
            != plan.template_span
            || domains.len() != plan.parameters.len()
        {
            return Err("全域型Domainの元template・軸数が違う".into());
        }
        for (&domain, parameter) in domains.iter().zip(&plan.parameters) {
            self.tick()?;
            let node = graph.get(domain)?;
            if node.arguments != [template]
                || graph.context_at(domain.0) != parameter.context
                || !matches!(&node.rule, Rule::Input { kind: "law", location: Location::Law { span } } if *span == parameter.binder)
                || !matches!(&node.payload, Some(Payload::TypeDomain {ty}) if *ty==parameter.kind.ty())
            {
                return Err("全域型Domainの元binder・型・Contextが違う".into());
            }
        }
        Ok(())
    }
}
