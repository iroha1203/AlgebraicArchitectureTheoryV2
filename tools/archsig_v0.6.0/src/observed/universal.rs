//! 元の量化種別・binder・実producerを保つZ/Q全域表示と、全称アフィン等値。
use super::*;
use crate::law::{
    ast::{QuantDomain, QuantKind, QuantSplit},
    model::Signature,
};
use crate::observed::affine::{self, NumberType, Parameter};
#[path = "universal_finite.rs"]
mod finite_decision;
#[path = "universal_validation.rs"]
pub(super) mod validation;

// 数値の係数軸と、列挙できない元型の量化軸を区別する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct UniversalParameter {
    pub binder: (usize, usize),
    pub name: String,
    pub context: super::super::call::Context,
    pub ty: Type,
}
impl UniversalParameter {
    fn affine_parameter(&self) -> Option<Parameter> {
        Some(Parameter {
            binder: self.binder,
            name: self.name.clone(),
            context: self.context,
            kind: number(&self.ty)?,
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct UniversalPlan {
    pub template_span: (usize, usize),
    pub body: usize,
    pub guard: Option<usize>,
    pub parameters: Vec<UniversalParameter>,
    pub family: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct AnalysisContext {
    pub(super) plan: UniversalPlan,
    pub(super) template: Option<NodeRef>,
    pub(super) domains: Vec<NodeRef>,
    pub(super) completions: Vec<(Fact, Scalar)>,
    pub(super) local_axes: Vec<LocalAxis>,
    pub(super) calls: Vec<ResolvedCall>,
    pub(super) iterations: Vec<(
        super::super::call::Context,
        super::super::call::Context,
        (usize, usize),
    )>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LocalAxis {
    pub parameter: UniversalParameter,
    pub domain: Option<NodeRef>,
    pub actual: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ResolvedCall {
    pub expression: usize,
    pub caller: super::super::call::Context,
    pub callee: super::super::call::Context,
}
pub(in crate::observed) struct UniversalSourceAnalysis {
    pub parameters: Vec<(String, Type)>,
    pub analysis: SourceAnalysis,
}
pub(in crate::observed) struct UniversalAnalysis {
    pub analysis: SourceAnalysis,
    pub classification: Option<affine::Universal>,
    // 数値残差の正規形は量化の真偽判定とは独立する。
    pub difference: Option<affine::Form>,
    pub comparison: Option<(usize, usize)>,
    pub comparison_expression: Option<usize>,
    pub value: Option<bool>,
    pub guard_value: Option<bool>,
    pub finite_dependency: Option<NodeRef>,
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
    // Parameterの数値型と、元ASTのforall/existsは別の情報として保つ。
    // Law自由parameterは全代入だが、明示existsを全称軸へ変えない。
    fn universal_parameter_quantifier_kind(
        &self,
        parameter: &UniversalParameter,
    ) -> Result<QuantKind, ValidationFailure> {
        for expression in &self.inputs.law().exprs {
            self.tick()?;
            if let ExprKind::Quant { kind, var, .. } = &expression.kind
                && var.span == parameter.binder
                && var.name == parameter.name
            {
                #[cfg(test)]
                data::observe_actual(
                    expression.span,
                    self.scoped_context
                        .get()
                        .or(self.context.get())
                        .unwrap_or_default(),
                    "quantifier_kind",
                    0,
                );
                return Ok(*kind);
            }
        }
        Ok(QuantKind::Forall)
    }
    fn universal_has_exists(&self, plan: &UniversalPlan) -> Result<bool, ValidationFailure> {
        for parameter in &plan.parameters {
            if self.universal_parameter_quantifier_kind(parameter)? == QuantKind::Exists {
                return Ok(true);
            }
        }
        Ok(false)
    }
    pub(in crate::observed) fn universal_unsupported_method(
        &self,
        plan: &UniversalPlan,
        guard_value: Option<bool>,
    ) -> Result<&'static str, ValidationFailure> {
        Ok(
            if plan
                .parameters
                .iter()
                .any(|p| p.affine_parameter().is_none())
            {
                "non-numeric infinite quantified decision"
            } else if self.universal_has_exists(plan)? {
                "Z/Q existential quantified decision"
            } else if plan.guard.is_some() && guard_value.is_none() {
                "parameter-dependent conditional affine equality"
            } else {
                "non-affine universal equality"
            },
        )
    }
    fn universal_closed_parameters(
        &self,
        plan: &UniversalPlan,
        predicate: &AffinePredicate,
    ) -> Result<Vec<Parameter>, ValidationFailure> {
        let mut parameters: Vec<Parameter> = plan
            .parameters
            .iter()
            .filter_map(UniversalParameter::affine_parameter)
            .collect();
        for bound in &predicate.bound_axes {
            self.tick()?;
            if !parameters.contains(bound) {
                parameters.push(bound.clone());
            }
        }
        Ok(parameters)
    }
    pub(super) fn universal_call_context(&self, id: usize) -> Option<super::super::call::Context> {
        let caller = self
            .scoped_context
            .get()
            .or(self.context.get())
            .unwrap_or_default();
        self.universal_context
            .borrow()
            .as_ref()
            .and_then(|context| {
                context
                    .calls
                    .iter()
                    .find(|call| call.expression == id && call.caller == caller)
                    .map(|call| call.callee)
            })
    }
    fn universal_graph_context(
        &self,
        graph: &Graph,
        plan: &UniversalPlan,
        template: NodeRef,
        domains: &[NodeRef],
        completions: Vec<(Fact, Scalar)>,
    ) -> Result<AnalysisContext, ValidationFailure> {
        let mut result = AnalysisContext {
            plan: plan.clone(),
            template: Some(template),
            domains: domains.to_vec(),
            completions,
            local_axes: Vec::new(),
            calls: Vec::new(),
            iterations: Vec::new(),
        };
        let cutoff = self.cutoff.get().min(graph.nodes.len());
        for (index, frame) in graph.frames.iter().enumerate() {
            self.tick()?;
            if frame.source.0 >= cutoff
                || frame.arguments.iter().any(|argument| argument.0 >= cutoff)
            {
                continue;
            }
            let source = graph.get(frame.source)?;
            if source.arguments.first() != Some(&template) {
                continue;
            }
            let span = self.expression_span(graph, frame.source)?;
            let id = *self
                .expressions
                .get(&span)
                .ok_or("局所全称callの元ASTがない")?;
            if self.named_view(id)?.is_none() || graph.context_at(frame.source.0) != frame.caller {
                return Err("局所全称callの実Frameが元構文と違う".into());
            }
            if result
                .calls
                .iter()
                .any(|call| call.expression == id && call.caller == frame.caller)
            {
                return Err("同じ元call・callerの実Frameが一意でない".into());
            }
            result.calls.push(ResolvedCall {
                expression: id,
                caller: frame.caller,
                callee: super::super::call::Context {
                    frame: Some(index),
                    iteration: None,
                    ..frame.caller
                },
            });
        }
        for (index, record) in graph.iterations.iter().enumerate() {
            self.tick()?;
            if record.source.0 >= cutoff || record.domain.0 >= cutoff {
                continue;
            }
            if graph.get(record.source)?.arguments.first() != Some(&template) {
                continue;
            }
            if record
                .caller
                .iteration
                .is_some_and(|parent| parent >= index)
                || graph.context_at(record.source.0) != record.caller
                || graph.context_at(record.domain.0) != record.caller
            {
                return Err("全域有限反復の元producer・親Contextが違う".into());
            }
            result.iterations.push((
                super::super::call::Context {
                    iteration: Some(index),
                    ..record.caller
                },
                record.caller,
                self.expression_span(graph, record.source)?,
            ));
        }
        for (index, node) in graph.nodes.iter().enumerate().take(cutoff) {
            self.tick()?;
            if !matches!(node.payload, Some(Payload::TypeDomain { .. }))
                || node.arguments.len() != 1
                || node.arguments[0] == template
            {
                continue;
            }
            let header = graph.get(node.arguments[0])?;
            if header.arguments.first() != Some(&template) {
                continue;
            }
            let axis = self.universal_local_domain_axis(
                graph,
                NodeRef(index),
                template,
                plan,
                &domains[..plan.parameters.len()],
            )?;
            if result
                .local_axes
                .iter()
                .any(|old| old.parameter == axis.parameter)
            {
                return Err("同じ局所全称binderの型Domainが重複する".into());
            }
            result.local_axes.push(axis);
        }
        Ok(result)
    }
    fn universal_binder_context(
        &self,
        active: &AnalysisContext,
        binder: (usize, usize),
        mut origin: super::super::call::Context,
    ) -> Result<super::super::call::Context, ValidationFailure> {
        while let Some((_, caller, span)) = active
            .iterations
            .iter()
            .find(|(context, _, _)| *context == origin)
        {
            self.tick()?;
            // 外側binderの出現は親のまま。反復body内で新しく量化したbinderは
            // 各実反復Contextに属するため、親へ移さない。
            let inherited = self.lexical_context(*span)?.iter().any(|(_, binding)| {
                match binding {
                    LexicalOrigin::Universal(id) => matches!(&self.inputs.law().exprs[*id].kind, ExprKind::Quant { var, .. } if var.span == binder),
                    _ => false,
                }
            });
            if !inherited {
                break;
            }
            origin = *caller;
        }
        Ok(origin)
    }
    fn universal_local_domain_axis(
        &self,
        graph: &Graph,
        domain: NodeRef,
        template: NodeRef,
        plan: &UniversalPlan,
        root_domains: &[NodeRef],
    ) -> Result<LocalAxis, ValidationFailure> {
        let node = graph.get(domain)?;
        let [header] = node.arguments.as_slice() else {
            return Err("局所型Domainの元headerが一つでない".into());
        };
        let source = graph.get(*header)?;
        let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &source.payload
        else {
            return Err("局所型Domainのheaderが元Sourceでない".into());
        };
        let id = *self
            .expressions
            .get(span)
            .ok_or("局所型Domainの元量化がない")?;
        let ExprKind::Quant {
            var,
            split:
                QuantSplit::Fixed {
                    domain: QuantDomain::Type(_),
                    ..
                },
            ..
        } = &self.inputs.law().exprs[id].kind
        else {
            return Err("局所型Domainの元構文が型全称でない".into());
        };
        let ty = self.inputs.law().quantifier_types[id]
            .as_ref()
            .ok_or("局所全称型がない")?;
        if !self.universal_symbolic_type(ty)? {
            return Err("局所型Domainが有限型である".into());
        }
        let context = graph.context_at(header.0);
        if graph.context_at(domain.0) != context
            || header.0 >= domain.0
            || source.arguments.first() != Some(&template)
            || source.arguments.get(1..1 + root_domains.len()) != Some(root_domains)
            || plan
                .parameters
                .iter()
                .any(|p| p.binder == var.span && p.context == context)
            || !matches!(&node.payload,Some(Payload::TypeDomain{ty:actual}) if actual==ty)
            || !matches!(&node.rule,Rule::Input{kind:"law",location:Location::Law{span}} if *span==var.span)
        {
            return Err("局所全称Domainの元binder・型・実Contextが違う".into());
        }
        Ok(LocalAxis {
            parameter: UniversalParameter {
                binder: var.span,
                name: var.name.clone(),
                context,
                ty: ty.clone(),
            },
            domain: Some(domain),
            actual: true,
        })
    }
    pub(in crate::observed) fn universal_source_domain_refs(
        &self,
        graph: &Graph,
        node: &Node,
        template: NodeRef,
        plan: &UniversalPlan,
    ) -> Result<Vec<NodeRef>, ValidationFailure> {
        if node.arguments.first() != Some(&template) {
            return Err("全域Sourceの元templateが違う".into());
        }
        let mut domains = Vec::new();
        for &reference in &node.arguments[1..] {
            self.tick()?;
            if !matches!(
                graph.get(reference)?.payload,
                Some(Payload::TypeDomain { .. })
            ) {
                break;
            }
            domains.push(reference);
        }
        self.universal_check_domains(graph, template, &domains, plan)?;
        let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &node.payload
        else {
            return Err("局所Domain列を持つ元Sourceがない".into());
        };
        let root = &domains[..plan.parameters.len()];
        let registry = self.universal_graph_context(graph, plan, template, root, Vec::new())?;
        let mut path = vec![(self.current_context(graph), *span)];
        let mut current = self.current_context(graph);
        while let Some(index) = current.frame {
            self.tick()?;
            let frame = graph
                .frames
                .get(index)
                .ok_or("局所Domain列の実Frameがない")?;
            if frame.caller.frame.is_some_and(|parent| parent >= index) {
                return Err("局所Domain列の親Frameが先行しない".into());
            }
            path.push((frame.caller, self.expression_span(graph, frame.source)?));
            current = frame.caller;
        }
        path.reverse();
        let mut expected = root.to_vec();
        for (context, span) in path {
            for (_, binding) in self.lexical_context(span)? {
                self.tick()?;
                let LexicalOrigin::Universal(id) = binding else {
                    continue;
                };
                let ExprKind::Quant { var, .. } = &self.inputs.law().exprs[id].kind else {
                    unreachable!()
                };
                let binder_context = self.universal_binder_context(&registry, var.span, context)?;
                if plan.parameters.iter().any(|parameter| {
                    parameter.binder == var.span && parameter.context == binder_context
                }) {
                    continue;
                }
                let axis = registry
                    .local_axes
                    .iter()
                    .find(|axis| {
                        axis.parameter.binder == var.span
                            && axis.parameter.context == binder_context
                    })
                    .ok_or("元lexical全称に先行する局所型Domainがない")?;
                let domain = axis.domain.ok_or("実局所型Domainがない")?;
                if !expected.contains(&domain) {
                    expected.push(domain);
                }
            }
        }
        if domains != expected {
            return Err("全域Sourceの局所型Domain列が元lexical/実call順と違う".into());
        }
        Ok(domains)
    }
    pub(in crate::observed) fn universal_local_parameter(
        &self,
        graph: &Graph,
        plan: &UniversalPlan,
        template: NodeRef,
        domains: &[NodeRef],
        id: usize,
    ) -> Result<Option<UniversalParameter>, ValidationFailure> {
        self.universal_check_domains(graph, template, domains, plan)?;
        let ExprKind::Quant {
            var,
            split:
                QuantSplit::Fixed {
                    domain: QuantDomain::Type(_),
                    ..
                },
            ..
        } = &self.inputs.law().exprs[id].kind
        else {
            return Ok(None);
        };
        let ty = self.inputs.law().quantifier_types[id]
            .as_ref()
            .ok_or("局所型がない")?;
        if !self.universal_symbolic_type(ty)? {
            return Ok(None);
        }
        let context = self.current_context(graph);
        Ok((!plan
            .parameters
            .iter()
            .any(|p| p.binder == var.span && p.context == context))
        .then(|| UniversalParameter {
            binder: var.span,
            name: var.name.clone(),
            context,
            ty: ty.clone(),
        }))
    }
    pub(in crate::observed) fn universal_local_retains_comparison(
        &self,
        graph: &Graph,
        plan: &UniversalPlan,
        template: NodeRef,
        domains: &[NodeRef],
        id: usize,
        bindings: &[Binding],
    ) -> Result<bool, ValidationFailure> {
        if self
            .universal_local_parameter(graph, plan, template, domains, id)?
            .is_none()
        {
            return Ok(true);
        }
        Ok(self
            .universal_source_analysis(
                graph,
                self.inputs.law().exprs[id].span,
                bindings,
                plan,
                domains,
                template,
            )?
            .analysis
            .comparison
            .is_some())
    }
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
            self.with_universal_graph(graph, original, || self.frame_arguments(graph, index))?;
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
                        condition_failed: graph
                            .get(*reference)?
                            .reasons
                            .iter()
                            .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. })),
                        condition_pending: analysis.condition_pending,
                        symbolic: analysis.symbolic,
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
        if !numeric::is_numeric_type(ty, &self.control)? || value.ty() != *ty {
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
                || !numeric::is_numeric_type(&field.ty, &self.control)?
                || value.ty() != field.ty
            {
                return Err("全域数値補完の元欠測slot・型が違う".into());
            }
        }
        self.with_universal_graph(
            graph,
            self.universal_graph_context(graph, &plan, template, domains, values.to_vec())?,
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
            var,
            split:
                QuantSplit::Fixed {
                    domain: QuantDomain::Type(_),
                    body,
                },
            ..
        } = &self.inputs.law().exprs[id].kind
        else {
            return Ok(None);
        };
        let ty = self.inputs.law().quantifier_types[id]
            .as_ref()
            .ok_or("全域binder型がない")?;
        if !self.universal_symbolic_type(ty)? {
            return Ok(None);
        }
        if self.universal_context.borrow().is_none() {
            // 未展開callの静的bodyは実Contextをまだ持たない。
            // validationのcallerや既定request 0をcalleeの出現として記録しない。
            let actual_context = self.scoped_context.get();
            let context = actual_context.unwrap_or_default();
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
                    local_axes: Vec::new(),
                    calls: Vec::new(),
                    iterations: Vec::new(),
                },
                || {
                    let mut scope = base.clone();
                    self.universal_extend_scope(&mut scope, self.inputs.law().exprs[id].span)?;
                    let mut local = self.copy_variables(variables)?;
                    for parameter in &plan.parameters {
                        local.insert(
                            parameter.name.clone(),
                            self.universal_parameter_value(
                                parameter.binder,
                                &parameter.name,
                                &parameter.ty.clone(),
                                &scope,
                            )?,
                        );
                    }
                    let mut value = self.scoped_ast(plan.body, &local, &scope, reading)?;
                    // 全称軸は、bodyでその変数を使用しない場合も元量化に属する。
                    value.scope.merge(&scope);
                    value.known_value = match value.comparison.as_ref() {
                        Some(predicate)
                            if predicate.op == BinOp::Eq
                                && !self.universal_has_exists(&plan)?
                                && plan
                                    .parameters
                                    .iter()
                                    .all(|p| p.affine_parameter().is_some()) =>
                        {
                            affine::universal_equality(
                                Some(&predicate.left),
                                Some(&predicate.right),
                                &self.universal_closed_parameters(&plan, predicate)?,
                                &self.control,
                            )?
                            .and_then(|classification| classification.value)
                            .map(Scalar::Bool)
                        }
                        _ => value.known_value,
                    };
                    for parameter in plan
                        .parameters
                        .iter()
                        .rev()
                        .filter(|p| p.affine_parameter().is_none())
                    {
                        value.known_value = self.universal_opaque_constant(
                            self.universal_parameter_quantifier_kind(parameter)?,
                            &parameter.ty,
                            value.known_value.as_ref(),
                        );
                    }
                    value.affine = None;
                    value.comparison = None;
                    if actual_context.is_none() {
                        for quantifier in &mut value.scope.quantifiers {
                            self.tick()?;
                            if quantifier.domain.is_none()
                                && plan.parameters.iter().any(|parameter| {
                                    parameter.binder == quantifier.occurrence
                                        && parameter.name == quantifier.name
                                })
                            {
                                quantifier.context = None;
                            }
                        }
                    }
                    value.scalar_scope = value.known_value.as_ref().map(|_| value.scope.clone());
                    Ok(Some(value))
                },
            );
        }
        let active = self
            .universal_context
            .borrow()
            .clone()
            .ok_or("全域分析contextがない")?;
        let root_axis = active.plan.parameters.iter().any(|p| p.binder == var.span);
        if !root_axis {
            return self
                .universal_local_quantifier_value(id, variables, base, reading)
                .map(Some);
        }
        let mut local = self.copy_variables(variables)?;
        local.insert(
            var.name.clone(),
            self.universal_parameter_value(var.span, &var.name, ty, base)?,
        );
        let mut value = self.scoped_ast(*body, &local, base, reading)?;
        if number(ty).is_none() {
            let ExprKind::Quant { kind, .. } = self.inputs.law().exprs[id].kind else {
                unreachable!()
            };
            value.known_value =
                self.universal_opaque_constant(kind, ty, value.known_value.as_ref());
        }
        value.scalar_scope = value.known_value.as_ref().map(|_| value.scope.clone());
        value.affine = None;
        value.comparison = None;
        Ok(Some(value))
    }
    fn universal_local_quantifier_value(
        &self,
        id: usize,
        variables: &BTreeMap<String, SourceValue>,
        base: &Scope,
        reading: &str,
    ) -> Result<SourceValue, ValidationFailure> {
        let ExprKind::Quant {
            kind,
            var,
            split: QuantSplit::Fixed { body, .. },
            ..
        } = &self.inputs.law().exprs[id].kind
        else {
            unreachable!()
        };
        let ty = self.inputs.law().quantifier_types[id]
            .as_ref()
            .ok_or("局所全称型がない")?;
        let mut context = self
            .universal_context
            .borrow()
            .clone()
            .ok_or("局所全称のcaller Planがない")?;
        let actual = self.scoped_context.get();
        let origin = actual.or(self.context.get()).unwrap_or_default();
        let axis = context
            .local_axes
            .iter()
            .find(|axis| axis.parameter.binder == var.span && axis.parameter.context == origin)
            .cloned()
            .unwrap_or(LocalAxis {
                parameter: UniversalParameter {
                    binder: var.span,
                    name: var.name.clone(),
                    context: origin,
                    ty: ty.clone(),
                },
                domain: None,
                actual: actual.is_some(),
            });
        if !context
            .local_axes
            .iter()
            .any(|old| old.parameter == axis.parameter)
        {
            context.local_axes.push(axis.clone());
        }
        let mut scope = base.clone();
        scope.assignments = true;
        scope.add_quantifier(Quantifier {
            kind: *kind,
            name: var.name.clone(),
            ty: ty.clone(),
            domain: axis.domain,
            occurrence: var.span,
            context: axis.actual.then_some(origin),
        });
        self.with_universal(context, || {
            let mut local = self.copy_variables(variables)?;
            for value in local.values_mut() {
                self.tick()?;
                value.scope.merge(&scope);
            }
            local.insert(
                var.name.clone(),
                self.universal_parameter_value(var.span, &var.name, ty, &scope)?,
            );
            let mut value = self.scoped_ast(*body, &local, &scope, reading)?;
            value.scope.merge(&scope);
            if *kind == QuantKind::Forall
                && let Some(parameter) = axis.parameter.affine_parameter()
                && let Some(predicate) = value.comparison.as_ref()
                && predicate.op == BinOp::Eq
                && let Some(partial) = affine::partial_forall(
                    Some(&predicate.left),
                    Some(&predicate.right),
                    std::slice::from_ref(&parameter),
                    &self.control,
                )?
            {
                value.known_value = partial.value.map(Scalar::Bool).or(value.known_value);
            }
            if *kind == QuantKind::Exists || axis.parameter.affine_parameter().is_none() {
                value.comparison = None;
            } else if let Some(predicate) = &mut value.comparison
                && let Some(parameter) = axis.parameter.affine_parameter()
                && !predicate.bound_axes.contains(&parameter)
            {
                predicate.bound_axes.insert(0, parameter);
            }
            if axis.parameter.affine_parameter().is_none() {
                value.known_value =
                    self.universal_opaque_constant(*kind, ty, value.known_value.as_ref());
            }
            value.affine = None;
            value.scalar_scope = value.known_value.as_ref().map(|_| value.scope.clone());
            Ok(value)
        })
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
        let origin = self.universal_binder_context(
            context,
            binder,
            self.scoped_context
                .get()
                .or(self.context.get())
                .unwrap_or_default(),
        )?;
        let parameter = context
            .plan
            .parameters
            .iter()
            .find(|parameter| {
                parameter.binder == binder && parameter.name == name && parameter.ty.clone() == *ty
            })
            .or_else(|| {
                context
                    .local_axes
                    .iter()
                    .find(|axis| {
                        axis.parameter.binder == binder
                            && axis.parameter.name == name
                            && axis.parameter.ty.clone() == *ty
                            && axis.parameter.context == origin
                    })
                    .map(|axis| &axis.parameter)
            })
            .ok_or_else(|| ValidationFailure::UnsupportedExpression {
                location: Location::Law { span: binder },
                feature: "call展開内で追加されるZ/Q全称binderの全域Plan".into(),
            })?;
        Ok(SourceValue {
            condition_failed: false,
            condition_pending: false,
            symbolic: None,
            comparison: None,
            affine: parameter
                .affine_parameter()
                .map(|p| affine::parameter(ty, &p, &self.control))
                .transpose()?
                .flatten()
                .map(Box::new),
            scope: base.clone(),
            known_value: None,
            support: Vec::new(),
            scalar_scope: None,
        })
    }
    pub(super) fn universal_extend_scope(
        &self,
        scope: &mut Scope,
        span: (usize, usize),
    ) -> Result<(), ValidationFailure> {
        if let Some(context) = self.universal_context.borrow().as_ref() {
            scope.assignments = true;
            for (index, parameter) in context.plan.parameters.iter().enumerate() {
                self.tick()?;
                scope.add_quantifier(Quantifier {
                    kind: self.universal_parameter_quantifier_kind(parameter)?,
                    name: parameter.name.clone(),
                    ty: parameter.ty.clone(),
                    domain: context.domains.get(index).copied(),
                    occurrence: parameter.binder,
                    context: Some(parameter.context),
                });
            }
            let origin = self
                .scoped_context
                .get()
                .or(self.context.get())
                .unwrap_or_default();
            let lexical = self.lexical_context(span)?;
            for axis in &context.local_axes {
                self.tick()?;
                let binder_context =
                    self.universal_binder_context(context, axis.parameter.binder, origin)?;
                let enclosed = lexical.iter().any(|(_, binding)| match binding {
                    LexicalOrigin::Universal(id) => matches!(&self.inputs.law().exprs[*id].kind, ExprKind::Quant { var, .. } if var.span == axis.parameter.binder),
                    _ => false,
                });
                if axis.parameter.context != binder_context || !enclosed {
                    continue;
                }
                scope.add_quantifier(Quantifier {
                    kind: self.universal_parameter_quantifier_kind(&axis.parameter)?,
                    name: axis.parameter.name.clone(),
                    ty: axis.parameter.ty.clone(),
                    domain: axis.domain,
                    occurrence: axis.parameter.binder,
                    context: axis.actual.then_some(axis.parameter.context),
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
            if !self.universal_symbolic_type(&param.ty.erase())? {
                return Ok(None);
            }
            parameters.push(UniversalParameter {
                binder: param.span,
                name: param.name.clone(),
                context,
                ty: param.ty.erase(),
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
                var,
                split:
                    QuantSplit::Fixed {
                        domain: QuantDomain::Type(_),
                        body,
                    },
                ..
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
            if !self.universal_symbolic_type(ty)? {
                break;
            }
            plan.parameters.push(UniversalParameter {
                binder: var.span,
                name: var.name.clone(),
                context,
                ty: ty.clone(),
            });
            plan.body = *body;
        }
        Ok(())
    }
    fn with_universal_graph<T>(
        &self,
        graph: &Graph,
        context: AnalysisContext,
        run: impl FnOnce() -> Result<T, ValidationFailure>,
    ) -> Result<T, ValidationFailure> {
        self.validation_graph_session(graph, || self.with_universal(context, run))
    }
    pub(in crate::observed) fn with_universal<T, E>(
        &self,
        context: AnalysisContext,
        run: impl FnOnce() -> Result<T, E>,
    ) -> Result<T, E> {
        self.validation_session(|| {
            let old = self.universal_context.replace(Some(context));
            let result = run();
            self.universal_context.replace(old);
            result
        })
    }
    // 通常の有限評価へ渡す構文。型域の受付はquantifier::specで検査する。
    pub(in crate::observed) fn universal_symbolic_type(
        &self,
        ty: &Type,
    ) -> Result<bool, ValidationFailure> {
        Ok(number(ty).is_some()
            || !super::super::finite::supported(ty, self.inputs.law(), &self.control)?)
    }
    fn universal_opaque_constant(
        &self,
        kind: QuantKind,
        ty: &Type,
        value: Option<&Scalar>,
    ) -> Option<Scalar> {
        // 空文字列・空List/Set・noneは、これらの型を必ずinhabitedにする。
        if matches!(
            ty,
            Type::Text | Type::List(_) | Type::Set(_) | Type::Option(_)
        ) {
            return value.cloned();
        }
        match (kind, value) {
            (QuantKind::Forall, Some(Scalar::Bool(true))) => Some(Scalar::Bool(true)),
            (QuantKind::Exists, Some(Scalar::Bool(false))) => Some(Scalar::Bool(false)),
            _ => None,
        }
    }
    pub(in crate::observed) fn universal_finite_syntax(
        &self,
        id: usize,
    ) -> Result<bool, ValidationFailure> {
        Ok(match &self.inputs.law().exprs[id].kind {
            ExprKind::SetComp { .. } => true,
            ExprKind::Quant {
                split:
                    QuantSplit::Fixed {
                        domain: QuantDomain::In(_),
                        ..
                    },
                ..
            } => true,
            ExprKind::Quant { .. } => !self.universal_symbolic_type(
                self.inputs.law().quantifier_types[id]
                    .as_ref()
                    .ok_or("量化元型がない")?,
            )?,
            _ => false,
        })
    }
    pub(in crate::observed) fn universal_template_source_analysis(
        &self,
        graph: &Graph,
        plan: &UniversalPlan,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<UniversalSourceAnalysis, ValidationFailure> {
        self.with_universal_graph(
            graph,
            AnalysisContext {
                plan: plan.clone(),
                template: None,
                domains: Vec::new(),
                completions: Vec::new(),
                local_axes: Vec::new(),
                calls: Vec::new(),
                iterations: Vec::new(),
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
        self.validation_graph_session(graph, || {
            self.universal_check_domains(graph, template, domains, plan)?;
            self.with_universal_graph(
                graph,
                self.universal_graph_context(
                    graph,
                    plan,
                    template,
                    domains,
                    self.universal_completions(template),
                )?,
                || self.universal_analyze_at(graph, span, bindings),
            )
        })
    }
    fn universal_analyze_at(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<UniversalSourceAnalysis, ValidationFailure> {
        self.tick()?;
        let analysis = self.universal_source_with_context(graph, span, bindings)?;
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
            if self.universal_symbolic_type(&parameter.ty.erase())?
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
    pub(super) fn universal_source_with_context(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<SourceAnalysis, ValidationFailure> {
        self.validation_graph_session(graph, || {
            self.tick()?;
            let context = self.current_context(graph);
            let cutoff = self.cutoff.get().min(graph.nodes.len());
            let active = self
                .universal_context
                .borrow()
                .clone()
                .ok_or("全域sourceの分析Contextがない")?;
            let cached = self
                .cache
                .borrow()
                .universal_sources
                .iter()
                .find(|(c, l, at, b, a, _)| {
                    *c == context && *l == cutoff && *at == span && b == bindings && a == &active
                })
                .map(|entry| entry.5.clone());
            if let Some(value) = cached {
                self.tick()?;
                return Ok(value);
            }
            let value = self.universal_uncached_source(graph, span, bindings)?;
            self.tick()?;
            self.cache.borrow_mut().universal_sources.push((
                context,
                cutoff,
                span,
                bindings.to_vec(),
                active,
                value.clone(),
            ));
            Ok(value)
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
            self.with_universal_graph(
                graph,
                self.universal_graph_context(
                    graph,
                    &plan,
                    template,
                    domains,
                    self.universal_completions(template),
                )?,
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
                            difference: None,
                            comparison: None,
                            comparison_expression: None,
                            value: Some(true),
                            guard_value,
                            finite_dependency: None,
                        });
                    }
                    let mut analysis = self.universal_uncached_source(
                        graph,
                        self.inputs.law().exprs[plan.body].span,
                        bindings,
                    )?;
                    let predicate = analysis.comparison.as_ref();
                    let difference = match predicate {
                        Some(predicate) if predicate.op == BinOp::Eq => affine::binary(
                            BinOp::Sub,
                            Some(&predicate.left),
                            Some(&predicate.right),
                            &self.control,
                        )?,
                        _ => None,
                    };
                    let classification = match predicate {
                        Some(predicate)
                            if predicate.op == BinOp::Eq
                                && !self.universal_has_exists(&plan)?
                                && plan
                                    .parameters
                                    .iter()
                                    .all(|p| p.affine_parameter().is_some()) =>
                        {
                            let parameters = self.universal_closed_parameters(&plan, predicate)?;
                            affine::universal_equality(
                                Some(&predicate.left),
                                Some(&predicate.right),
                                &parameters,
                                &self.control,
                            )?
                        }
                        _ => None,
                    };
                    let comparison_expression = predicate.map(|predicate| predicate.expression);
                    let comparison = comparison_expression.and_then(|id| {
                        match self.inputs.law().exprs[id].kind {
                            ExprKind::Binary { lhs, rhs, .. } => Some((lhs, rhs)),
                            _ => None,
                        }
                    });
                    let mut body_value = classification
                        .as_ref()
                        .and_then(|classification| classification.value)
                        .or(match analysis.known_value.as_ref() {
                            Some(Scalar::Bool(value)) => Some(*value),
                            _ => None,
                        });
                    // 実有限域の全caseは、元のpointwise導出が完成した後でだけ使う。
                    // Sourceの静的分析から有限域のRefや実反復Contextを捏造しない。
                    if let Some(actual) = self.universal_completed_pointwise(
                        graph,
                        template,
                        plan.template_span,
                        bindings,
                    )? {
                        self.recheck_evaluation(graph, actual)?;
                        analysis.scope.merge(&graph.get(actual)?.scope);
                    }
                    for parameter in plan
                        .parameters
                        .iter()
                        .rev()
                        .filter(|p| p.affine_parameter().is_none())
                    {
                        body_value = self
                            .universal_opaque_constant(
                                self.universal_parameter_quantifier_kind(parameter)?,
                                &parameter.ty,
                                body_value.map(Scalar::Bool).as_ref(),
                            )
                            .and_then(|v| {
                                if let Scalar::Bool(b) = v {
                                    Some(b)
                                } else {
                                    None
                                }
                            });
                    }
                    let mut finite_dependency = None;
                    if body_value.is_none()
                        && !analysis.condition_failed
                        && !analysis.condition_pending
                        && !self.universal_has_exists(&plan)?
                    {
                        if let Some((decision, dependency)) =
                            self.universal_finite_decision(graph, template, &plan, bindings)?
                        {
                            body_value = Some(decision);
                            finite_dependency = Some(dependency);
                        }
                    }
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
                        difference,
                        comparison,
                        comparison_expression,
                        value,
                        guard_value,
                        finite_dependency,
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
        let result = self.with_universal_graph(
            graph,
            self.universal_graph_context(graph, &plan, template, domains, Vec::new())?,
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
                        bound_axes: predicate.bound_axes.clone(),
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
        let result = self.with_universal_graph(
            graph,
            self.universal_graph_context(graph, &plan, template, domains, Vec::new())?,
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
                        let lexical = self.lexical_context(span)?;
                        let declared_binder = formal
                            .iter()
                            .find(|parameter| {
                                parameter.name == *name && parameter.ty.erase() == *ty
                            })
                            .map(|parameter| parameter.span);
                        let binder = lexical
                            .iter()
                            .rev()
                            .find_map(|(local, origin)| {
                                if local == name {
                                    match origin {
                                        LexicalOrigin::Universal(id) => {
                                            match &self.inputs.law().exprs[*id].kind {
                                                ExprKind::Quant { var, .. } => Some(var.span),
                                                _ => None,
                                            }
                                        }
                                        _ => None,
                                    }
                                } else {
                                    None
                                }
                            })
                            .or(declared_binder)
                            .ok_or("具体反例の元自由binderがない")?;
                        let (parameter, value) = assignment
                            .iter()
                            .find(|(parameter, _)| {
                                parameter.name == *name
                                    && parameter.kind.ty() == *ty
                                    && parameter.binder == binder
                                    && parameter.context == graph.context_at(original.0)
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
            || domains.len() < plan.parameters.len()
        {
            return Err("全域型Domainの元template・軸数が違う".into());
        }
        for (&domain, parameter) in domains
            .iter()
            .take(plan.parameters.len())
            .zip(&plan.parameters)
        {
            self.tick()?;
            let node = graph.get(domain)?;
            if node.arguments != [template]
                || graph.context_at(domain.0) != parameter.context
                || !matches!(&node.rule, Rule::Input { kind: "law", location: Location::Law { span } } if *span == parameter.binder)
                || !matches!(&node.payload, Some(Payload::TypeDomain {ty}) if *ty==parameter.ty.clone())
            {
                return Err("全域型Domainの元binder・型・Contextが違う".into());
            }
        }
        for (index, &domain) in domains.iter().enumerate().skip(plan.parameters.len()) {
            self.tick()?;
            if domains[..index].contains(&domain) {
                return Err("全域Sourceの局所Domain参照が重複する".into());
            }
            self.universal_local_domain_axis(
                graph,
                domain,
                template,
                plan,
                &domains[..plan.parameters.len()],
            )?;
        }
        Ok(())
    }
}
