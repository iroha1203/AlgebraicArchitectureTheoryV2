//! 明示束縛の参照・原始 field と Z/Bool 演算を原 AST から評価する。
use super::{
    PreparedObserved,
    control::{Checkpoint, Control, StopReason},
    data,
    environment::{
        Environment, SourceAnalysis, conditional_branch, is_boolean_binary, is_comparison,
        partial_binary, scalar_from, supports_binary, unary,
    },
    input::InputSources,
    numeric, prepare_observed,
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::{
    archmap::Slot,
    issue::Location,
    law::{
        ast::{BinOp, ExprId, ExprKind, Role, UnOp},
        model::{Declaration, Param, Signature},
    },
    types::Type,
};
use std::collections::BTreeMap;

pub fn evaluate_observed_bytes(
    sources: InputSources,
    texts: &[&str],
    control: &mut Control,
) -> Result<ObservedEvaluation, EvaluationFailure> {
    let prepared = prepare_observed(sources, texts, control).map_err(EvaluationFailure::Prepare)?;
    evaluate_observed(prepared, control)
}

#[derive(Debug)]
enum Failure {
    Stop(StopReason),
    Internal(String),
    NotImplemented { location: Location, feature: String },
}
impl From<ValidationFailure> for Failure {
    fn from(v: ValidationFailure) -> Self {
        match v {
            ValidationFailure::Internal(s) => Self::Internal(s),
            ValidationFailure::Stop(s) => Self::Stop(s),
            ValidationFailure::UnsupportedExpression { location, feature } => {
                Self::NotImplemented { location, feature }
            }
        }
    }
}
impl From<String> for Failure {
    fn from(s: String) -> Self {
        Self::Internal(s)
    }
}
impl From<StopReason> for Failure {
    fn from(s: StopReason) -> Self {
        Self::Stop(s)
    }
}
#[derive(Clone, Debug)]
struct Evaluated {
    expression: NodeRef,
    evaluation: NodeRef,
    value: Option<NodeRef>,
    scope: Scope,
    support: Vec<Fact>,
    reasons: Vec<Reason>,
    comparison: Option<(NodeRef, NodeRef)>,
    residual: Option<NodeRef>,
}
/// commit 済みの元式。未検査の分析結果とは区別し、通常値には使用しない。
#[derive(Clone, Debug)]
struct SourceHandle {
    expression: NodeRef,
    scope: Scope,
    known_value: Option<Scalar>,
    missing: Option<Reason>,
}
struct Evaluator<'a, 'b> {
    environment: &'a Environment<'a>,
    graph: &'b mut Graph,
    control: &'b mut Control,
    request: &'a Request,
    declaration: &'a Declaration,
    bindings: Vec<Binding>,
    lexical: BTreeMap<String, Evaluated>,
    formal: BTreeMap<String, Evaluated>,
    base: Scope,
    // この Request で挿入済みの node が保持する評価範囲。root の完成とは独立。
    retained_scope: Scope,
    reasons: Vec<Reason>,
    completed: BTreeMap<ExprId, Evaluated>,
    answer_evaluation: Option<NodeRef>,
    sources: BTreeMap<(usize, usize), SourceHandle>,
}
impl Evaluator<'_, '_> {
    fn tick(&mut self, point: Checkpoint) -> Result<(), Failure> {
        self.control.checkpoint(point).map_err(Failure::Stop)
    }
    fn push(&mut self, node: Node) -> Result<NodeRef, Failure> {
        self.environment.validate(self.graph, &node)?;
        let previous_nodes = self.graph.nodes.len();
        let scope = node.scope.clone();
        let result = self.graph.push(node).map_err(Failure::from);
        if self.graph.nodes.len() > previous_nodes {
            // 挿入後の post checkpoint が停止しても、既存 node の範囲を記録する。
            // 既に検査・保持したデータの転記であり、新しい意味導出を行わない。
            self.retained_scope.merge(&scope);
        }
        result
    }
    fn unsupported(&self, span: (usize, usize), feature: impl Into<String>) -> Failure {
        Failure::NotImplemented {
            location: Location::Law { span },
            feature: feature.into(),
        }
    }
    fn value(
        &mut self,
        value: Scalar,
        rule: Rule,
        arguments: Vec<NodeRef>,
        support: Vec<Fact>,
        scope: Scope,
    ) -> Result<NodeRef, Failure> {
        let ty = value.ty();
        self.push(Node {
            ty: NodeType::Value(ty),
            payload: Some(Payload::Scalar(value)),
            rule,
            arguments,
            support,
            evidence: vec![],
            judgment: None,
            scope,
            reasons: vec![],
        })
    }
    fn bind(&mut self, params: &[Param]) -> Result<(), Failure> {
        for p in params {
            self.tick(Checkpoint::FiniteIteration)?;
            let name = format!("bind.{}", p.name);
            let mut found = None;
            for argument in &self.request.arguments {
                self.tick(Checkpoint::FiniteIteration)?;
                if argument.name == name {
                    found = Some(argument);
                }
                self.tick(Checkpoint::FiniteIteration)?;
            }
            let Some(argument) = found else {
                return Err(
                    self.unsupported(p.span, format!("未束縛 parameter `{}` の全称評価", p.name))
                );
            };
            match &argument.value {
                Selector::Subject { snapshot, subject } => {
                    let s = self.environment.subject(snapshot, subject)?;
                    let scalar = Scalar::Subject {
                        snapshot: snapshot.clone(),
                        subject: subject.clone(),
                        entity: s.ty.clone(),
                    };
                    if scalar.ty() != p.ty.erase() {
                        return Err(Failure::Internal("解決済み束縛の型が合わない".into()));
                    }
                    // 動的 owner が残る入力を、確認済みの所属として消費しない。
                    for constraint in &self.request.constraints {
                        self.tick(Checkpoint::FiniteIteration)?;
                        if constraint.parameter == p.name && constraint.dynamic {
                            return Err(self.unsupported(p.span, "動的 owner 制約の評価"));
                        }
                        self.tick(Checkpoint::FiniteIteration)?;
                    }
                    let scope = self.environment.scope(s, &self.declaration.reading, None)?;
                    self.base.merge(&scope);
                    let r = self.value(
                        scalar,
                        Rule::Input {
                            kind: "subject",
                            location: Location::ArchMap {
                                pointer: s.pointer.clone(),
                                span: None,
                            },
                        },
                        vec![],
                        vec![Fact {
                            snapshot: snapshot.clone(),
                            subject: subject.clone(),
                            field: None,
                            atom: None,
                        }],
                        scope,
                    )?;
                    self.bindings.push(Binding {
                        name: p.name.clone(),
                        value: r,
                        ty: p.ty.erase(),
                    });
                }
                Selector::Answer { .. } => {
                    return Err(self.unsupported(p.span, "Answer 由来の束縛と公開射影の評価"));
                }
                Selector::Declaration { .. } => {
                    return Err(Failure::Internal(
                        "parameter に宣言 selector が残っている".into(),
                    ));
                }
            }
            self.tick(Checkpoint::FiniteIteration)?;
        }
        Ok(())
    }
    fn source(&mut self, span: (usize, usize), ty: Type) -> Result<SourceHandle, Failure> {
        if let Some(source) = self.sources.get(&span) {
            self.graph
                .expect(source.expression, &NodeType::Expression(ty))?;
            return Ok(source.clone());
        }
        // この照合中の SourceAnalysis/PendingMissing は、まだ canonical な理由でない。
        let analysis = self
            .environment
            .analyze_source(self.graph, span, &self.bindings)?;
        // 照合が完了した pending の実入力範囲は、Source commit 前の停止でも残す。
        // canonical Missing はまだ作らず、実在 Ref との atomic commit まで待つ。
        self.retained_scope.merge(&analysis.scope);
        let node = Node {
            ty: NodeType::Expression(ty),
            payload: Some(Payload::Expression {
                location: Location::Law { span },
                parameters: vec![],
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
            scope: analysis.scope.clone(),
            reasons: vec![],
        };
        self.environment.validate(self.graph, &node)?;
        let SourceAnalysis {
            scope,
            known_value,
            missing,
            ..
        } = analysis;
        let registry = &mut self.reasons;
        let retained = &mut self.retained_scope;
        let cache = &mut self.sources;
        let request = self.request.id.clone();
        self.graph.push_with_metadata(node, |expression| {
            // Source の実在 Ref と元 slot の理由を post checkpoint より先に同時確定する。
            // callback は検査済み metadata の転記のみで、入力を読まず新たに導出しない。
            let missing = missing.map(|pending| Reason {
                kind: ReasonKind::Missing,
                request,
                dependencies: vec![expression],
                missing: vec![pending.fact],
                location: Some(Location::Law { span }),
            });
            if let Some(reason) = &missing {
                registry.push(reason.clone());
            }
            retained.merge(&scope);
            cache.insert(
                span,
                SourceHandle {
                    expression,
                    scope,
                    known_value,
                    missing,
                },
            );
        })?;
        self.sources
            .get(&span)
            .cloned()
            .ok_or_else(|| Failure::Internal("Source commit cache がない".into()))
    }
    /// 対応済みの式だけを子→親で構成する。各 field は直ちに個別 commit する。
    fn prepare_source(&mut self, id: ExprId) -> Result<SourceHandle, Failure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            let expr = &self.environment.inputs.law().exprs[id];
            let span = expr.span;
            let ty = self
                .environment
                .inputs
                .law()
                .expr_type(id)
                .ok_or_else(|| Failure::Internal("元式の型がない".into()))?
                .clone();
            if let Some(source) = self.sources.get(&span) {
                self.graph
                    .expect(source.expression, &NodeType::Expression(ty))?;
                return Ok(source.clone());
            }
            self.tick(Checkpoint::FiniteIteration)?;
            match &expr.kind {
                ExprKind::Int(_) if matches!(ty, Type::Z | Type::Q | Type::Fp(_)) => {}
                ExprKind::Bool(_) => {}
                ExprKind::Dotted(_)
                    if data::expression(self.environment.inputs.law(), id, self.control)?
                        .is_some() =>
                {
                    self.environment
                        .composite_children(id)?
                        .ok_or_else(|| self.unsupported(span, "未対応Data constructor"))?;
                }
                ExprKind::Dotted(parts) => {
                    if parts.len() > 2 {
                        return Err(self.unsupported(span, "複数 field のドット列"));
                    }
                    let first = parts
                        .first()
                        .ok_or_else(|| Failure::Internal("空のドット式".into()))?;
                    let mut parameter = None;
                    for binding in &self.bindings {
                        self.control.checkpoint(Checkpoint::FiniteIteration)?;
                        if binding.name == first.name {
                            parameter = Some(binding.ty.clone());
                        }
                        self.control.checkpoint(Checkpoint::FiniteIteration)?;
                    }
                    if parameter.is_none()
                        && let Some(argument) = self.formal.get(&first.name)
                        && let NodeType::Evaluation(ty) = &self.graph.get(argument.evaluation)?.ty
                    {
                        parameter = Some(ty.clone());
                    }
                    if parameter.is_none()
                        && let Some((_, value)) = self.environment.iteration_argument(
                            self.graph,
                            first.span,
                            &first.name,
                            &self.bindings,
                        )?
                    {
                        parameter = Some(value.ty());
                    }
                    if parameter.is_none()
                        && let Some((_, _, binder)) =
                            self.environment.pattern_binding(first.span, &first.name)?
                    {
                        parameter = Some(binder.ty);
                    }
                    if parameter.is_none()
                        && let Some(rhs) = self.environment.lexical_rhs(first.span, &first.name)?
                    {
                        parameter = self.environment.inputs.law().expr_type(rhs).cloned();
                    }
                    let parameter = parameter.ok_or_else(|| {
                        self.unsupported(span, "束縛変数以外を先頭とするドット式")
                    })?;
                    let owner = self.source(first.span, parameter)?;
                    if parts.len() > 1 && !matches!(owner.known_value, Some(Scalar::Subject { .. }))
                    {
                        return Err(self.unsupported(span, "未確定の参照からの field 読取り"));
                    }
                    if parts.len() > 1
                        && !matches!(ty, Type::Bool | Type::Ref(_) | Type::Owned(_, _))
                        && !data::supported(&ty, self.environment.inputs.law(), self.control)?
                    {
                        return Err(self.unsupported(span, "Z/Bool/Ref 以外の原始 slot 評価"));
                    }
                }
                ExprKind::Field { base, .. } => {
                    let owner = self.prepare_source(*base)?;
                    if !matches!(owner.known_value, Some(Scalar::Subject { .. })) {
                        return Err(self.unsupported(span, "未確定の参照からの field 読取り"));
                    }
                    if !matches!(ty, Type::Bool | Type::Ref(_) | Type::Owned(_, _))
                        && !data::supported(&ty, self.environment.inputs.law(), self.control)?
                    {
                        return Err(self.unsupported(span, "Z/Bool/Ref 以外の原始 slot 評価"));
                    }
                }
                ExprKind::Quant { .. } => {
                    let spec =
                        super::quantifier::spec(self.environment.inputs.law(), id, self.control)?;
                    self.prepare_source(spec.domain)?;
                }
                ExprKind::SetComp { domain, .. } => {
                    self.prepare_source(*domain)?;
                }
                ExprKind::Match { scrutinee, .. } => {
                    self.prepare_source(*scrutinee)?;
                }
                ExprKind::Group(child) => {
                    self.prepare_source(*child)?;
                }
                ExprKind::Let { value, body, .. } => {
                    self.prepare_source(*value)?;
                    self.prepare_source(*body)?;
                }
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    self.prepare_source(*cond)?;
                    self.prepare_source(*then_branch)?;
                    self.prepare_source(*else_branch)?;
                }
                ExprKind::Unary { op, operand }
                    if (*op == UnOp::Neg && numeric::is_numeric_type(&ty, self.control)?)
                        || (*op == UnOp::Not && ty == Type::Bool) =>
                {
                    self.prepare_source(*operand)?;
                }
                ExprKind::Binary { op, lhs, rhs } => {
                    let input_ty = self
                        .environment
                        .inputs
                        .law()
                        .expr_type(*lhs)
                        .ok_or_else(|| Failure::Internal("二項演算の型".into()))?;
                    if !supports_binary(*op, input_ty, self.control)? {
                        return Err(self.unsupported(span, "対応済み Z/Bool 二項演算以外"));
                    }
                    self.prepare_source(*lhs)?;
                    self.prepare_source(*rhs)?;
                }
                ExprKind::Call { args, .. } if self.environment.named_view(id)?.is_some() => {
                    for &argument in args {
                        self.tick(Checkpoint::FiniteIteration)?;
                        self.prepare_source(argument)?;
                    }
                }
                ExprKind::Tuple(_)
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
                        .ok_or_else(|| self.unsupported(span, "数値組・射影・rat 以外の構成"))?;
                    for child in children {
                        self.tick(Checkpoint::FiniteIteration)?;
                        self.prepare_source(child)?;
                        self.tick(Checkpoint::FiniteIteration)?;
                    }
                }
                _ => return Err(self.unsupported(span, format!("式形 {:?}", expr.kind))),
            }
            let source = self.source(span, ty)?;
            self.tick(Checkpoint::FiniteIteration)?;
            Ok(source)
        })
    }
    // 一つの原式出現へ位置・型・値・子評価・支持・欠測・比較左右・残差を対応付ける。
    // 独立に照合する各要素を、この内部の DAG 構成点で明示して渡す。
    #[allow(clippy::too_many_arguments)]
    fn finish(
        &mut self,
        span: (usize, usize),
        ty: Type,
        value: Option<NodeRef>,
        children: Vec<Evaluated>,
        own_support: Vec<Fact>,
        missing: Option<Fact>,
        comparison: Option<(NodeRef, NodeRef)>,
        residual: Option<NodeRef>,
    ) -> Result<Evaluated, Failure> {
        let source = self
            .sources
            .get(&span)
            .cloned()
            .ok_or_else(|| Failure::Internal("評価前の Source がない".into()))?;
        self.graph
            .expect(source.expression, &NodeType::Expression(ty.clone()))?;
        if source.missing.as_ref().and_then(|r| r.missing.first()) != missing.as_ref() {
            return Err(Failure::Internal(
                "元 slot と commit 済み欠測理由が違う".into(),
            ));
        }
        let mut scope = source.scope;
        for child in &children {
            scope.merge(&child.scope);
        }
        if let Some(value) = value {
            scope.merge_quantifiers(&self.graph.get(value)?.scope);
        }
        let expression = source.expression;
        let mut support = own_support;
        let mut reasons = Vec::new();
        for child in &children {
            self.tick(Checkpoint::FiniteIteration)?;
            support.extend(child.support.iter().cloned());
            reasons.extend(child.reasons.iter().cloned());
            self.tick(Checkpoint::FiniteIteration)?;
        }
        support.sort();
        support.dedup();
        if let Some(reason) = source.missing {
            reasons.push(reason);
        }
        sort_reasons(&mut reasons);
        let evidence = if let Some(value) = value {
            self.graph.get(value)?.evidence.clone()
        } else {
            vec![]
        };
        let evaluation = self.push(Node {
            ty: NodeType::Evaluation(ty),
            payload: Some(Payload::Evaluation {
                expression,
                bindings: self.bindings.clone(),
                parts: vec![Part {
                    location: Location::Law { span },
                    value,
                    residual,
                    children: children.iter().map(|c| c.evaluation).collect(),
                }],
                value,
                applicability: "applicable",
            }),
            rule: Rule::Construction("evaluation"),
            arguments: std::iter::once(expression)
                .chain(children.iter().map(|c| c.evaluation))
                .chain(value)
                .collect(),
            support: support.clone(),
            evidence,
            judgment: None,
            scope: scope.clone(),
            reasons: reasons.clone(),
        })?;
        Ok(Evaluated {
            expression,
            evaluation,
            value,
            scope,
            support,
            reasons,
            comparison,
            residual,
        })
    }
    fn eval(&mut self, id: ExprId) -> Result<Evaluated, Failure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick(Checkpoint::Expression)?;
            self.prepare_source(id)?;
            #[cfg(test)]
            data::observe_actual(
                self.environment.inputs.law().exprs[id].span,
                self.graph.active,
                "expression",
                0,
            );
            let value = self.eval_inner(id)?;
            // post checkpoint が停止しても検査済みの値と Evaluation を保持する。
            self.completed.insert(id, value.clone());
            self.tick(Checkpoint::Expression)?;
            Ok(value)
        })
    }
    fn eval_inner(&mut self, id: ExprId) -> Result<Evaluated, Failure> {
        let expr = &self.environment.inputs.law().exprs[id];
        let span = expr.span;
        let ty = self
            .environment
            .inputs
            .law()
            .expr_type(id)
            .ok_or_else(|| Failure::Internal("原式の型がない".into()))?
            .clone();
        match &expr.kind {
            ExprKind::Int(n) if matches!(ty, Type::Z | Type::Q | Type::Fp(_)) => {
                let v = self.value(
                    numeric::literal(n, &ty, self.control)?,
                    Rule::Input {
                        kind: "law",
                        location: Location::Law { span },
                    },
                    vec![],
                    vec![],
                    self.base.clone(),
                )?;
                self.finish(span, ty, Some(v), vec![], vec![], None, None, None)
            }
            ExprKind::Bool(b) => {
                let v = self.value(
                    Scalar::Bool(*b),
                    Rule::Input {
                        kind: "law",
                        location: Location::Law { span },
                    },
                    vec![],
                    vec![],
                    self.base.clone(),
                )?;
                self.finish(span, ty, Some(v), vec![], vec![], None, None, None)
            }
            ExprKind::Dotted(_)
                if data::expression(self.environment.inputs.law(), id, self.control)?.is_some() =>
            {
                self.composite(id, span, ty)
            }
            ExprKind::Dotted(parts) => {
                if parts.len() > 2 {
                    return Err(self.unsupported(span, "複数 field のドット列"));
                }
                let Some(first) = parts.first() else {
                    return Err(Failure::Internal("空のドット式".into()));
                };
                let mut found = None;
                for binding in &self.bindings {
                    self.control.checkpoint(Checkpoint::FiniteIteration)?;
                    if binding.name == first.name {
                        found = Some(binding.clone());
                    }
                    self.control.checkpoint(Checkpoint::FiniteIteration)?;
                }
                // 宣言parameter と lexical alias を区別する。欠測の alias は
                // RHS Evaluation を指し、通常の Binding.value を捏造しない。
                let mut current = if let Some((input, known)) = self
                    .environment
                    .iteration_argument(self.graph, first.span, &first.name, &self.bindings)?
                {
                    let child = self.evaluated_reference(input)?;
                    self.lexical_result(first.span, known.ty(), Some(known), vec![child])?
                } else if let Some((input, known)) = self.environment.pattern_argument(
                    self.graph,
                    first.span,
                    &first.name,
                    &self.bindings,
                )? {
                    let child = self.evaluated_reference(input)?;
                    self.lexical_result(first.span, known.ty(), Some(known), vec![child])?
                } else if let Some(argument) = self.formal.get(&first.name).cloned() {
                    let NodeType::Evaluation(parameter_ty) =
                        &self.graph.get(argument.evaluation)?.ty
                    else {
                        return Err(Failure::Internal("実引数がEvaluationでない".into()));
                    };
                    self.finish(
                        first.span,
                        parameter_ty.clone(),
                        argument.value,
                        vec![argument],
                        vec![],
                        None,
                        None,
                        None,
                    )?
                } else if let Some(binding) = found {
                    self.finish(
                        first.span,
                        binding.ty.clone(),
                        Some(binding.value),
                        vec![],
                        self.graph.get(binding.value)?.support.clone(),
                        None,
                        None,
                        None,
                    )?
                } else if let Some(rhs) = self.lexical.get(&first.name).cloned() {
                    let ty = self
                        .environment
                        .inputs
                        .law()
                        .expr_type(
                            self.environment
                                .lexical_rhs(first.span, &first.name)?
                                .ok_or_else(|| {
                                    Failure::Internal("alias の元binderがない".into())
                                })?,
                        )
                        .ok_or_else(|| Failure::Internal("alias の元型がない".into()))?
                        .clone();
                    self.finish(
                        first.span,
                        ty,
                        rhs.value,
                        vec![rhs],
                        vec![],
                        None,
                        None,
                        None,
                    )?
                } else {
                    return Err(self.unsupported(span, "束縛変数以外を先頭とするドット式"));
                };
                for part in parts.iter().skip(1) {
                    self.tick(Checkpoint::FiniteIteration)?;
                    current = self.field(current, &part.name, (first.span.0, part.span.1))?;
                    self.tick(Checkpoint::FiniteIteration)?;
                }
                if parts.len() == 1 {
                    Ok(current)
                } else {
                    if self.graph.get(current.expression)?.ty != NodeType::Expression(ty) {
                        return Err(Failure::Internal("ドット式の解決型が違う".into()));
                    }
                    Ok(current)
                }
            }
            ExprKind::Field { base, name } => {
                let base = self.eval(*base)?;
                self.field(base, &name.name, span)
            }
            ExprKind::Quant { .. } => self.quantification(id),
            ExprKind::SetComp {
                elem,
                var: _,
                domain,
                filter,
            } => self.comprehension(*domain, *elem, *filter, span, ty),
            ExprKind::Match { scrutinee, arms } => {
                let input = self.eval(*scrutinee)?;
                let selected = data::select(
                    self.environment.inputs.law(),
                    id,
                    input.value.map(|v| self.graph.scalar(v)).transpose()?,
                    self.control,
                )?;
                let mut children = vec![input];
                let known = if let Some(arm) = selected {
                    let body = self.eval(arms[arm].body)?;
                    let known = body
                        .value
                        .map(|v| self.graph.scalar(v).cloned())
                        .transpose()?;
                    children.push(body);
                    known
                } else {
                    None
                };
                self.lexical_result(span, ty, known, children)
            }
            ExprKind::Let { name, value, body } => {
                let rhs = self.eval(*value)?;
                if self
                    .lexical
                    .insert(name.name.clone(), rhs.clone())
                    .is_some()
                {
                    return Err(Failure::Internal("let の名前が重複する".into()));
                }
                let result = self.eval(*body);
                self.lexical.remove(&name.name);
                let body = result?;
                let known = body
                    .value
                    .map(|r| self.graph.scalar(r).cloned())
                    .transpose()?;
                self.lexical_result(span, ty, known, vec![rhs, body])
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let condition = self.eval(*cond)?;
                let left = self.eval(*then_branch)?;
                let right = self.eval(*else_branch)?;
                let known = conditional_branch(
                    condition.value.map(|r| self.graph.scalar(r)).transpose()?,
                    left.value.map(|r| self.graph.scalar(r)).transpose()?,
                    right.value.map(|r| self.graph.scalar(r)).transpose()?,
                    self.control,
                )?;
                self.lexical_result(span, ty, known, vec![condition, left, right])
            }
            ExprKind::Group(child) => {
                let child = self.eval(*child)?;
                self.finish(span, ty, child.value, vec![child], vec![], None, None, None)
            }
            ExprKind::Unary { op, operand }
                if (*op == UnOp::Neg && numeric::is_numeric_type(&ty, self.control)?)
                    || (*op == UnOp::Not && ty == Type::Bool) =>
            {
                let operand = self.eval(*operand)?;
                let value = match operand.value {
                    Some(r) => Some(self.value(
                        unary(*op, self.graph.scalar(r)?, self.control)?,
                        Rule::Input {
                            kind: "law",
                            location: Location::Law { span },
                        },
                        if *op == UnOp::Not {
                            vec![operand.evaluation]
                        } else {
                            vec![r]
                        },
                        operand.support.clone(),
                        operand.scope.clone(),
                    )?),
                    None => None,
                };
                self.finish(span, ty, value, vec![operand], vec![], None, None, None)
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let input_ty = self
                    .environment
                    .inputs
                    .law()
                    .expr_type(*lhs)
                    .ok_or_else(|| Failure::Internal("二項演算の型".into()))?;
                if !supports_binary(*op, input_ty, self.control)? {
                    return Err(self.unsupported(span, "対応済み Z/Bool 二項演算以外"));
                }
                let left = self.eval(*lhs)?;
                let right = self.eval(*rhs)?;
                let mut scope = left.scope.clone();
                scope.merge(&right.scope);
                let mut support = left.support.clone();
                support.extend(right.support.iter().cloned());
                support.sort();
                support.dedup();
                let pair = left.value.zip(right.value);
                let comparison = pair.filter(|_| is_comparison(*op));
                let known_value = partial_binary(
                    *op,
                    left.value.map(|r| self.graph.scalar(r)).transpose()?,
                    right.value.map(|r| self.graph.scalar(r)).transpose()?,
                    self.control,
                )?;
                let value = if let Some(value) = known_value {
                    let arguments = if is_boolean_binary(*op) {
                        vec![left.evaluation, right.evaluation]
                    } else {
                        let (l, r) = pair.ok_or_else(|| {
                            Failure::Internal("既知二項演算の左右値がない".into())
                        })?;
                        vec![l, r]
                    };
                    Some(self.value(
                        value,
                        Rule::Input {
                            kind: "law",
                            location: Location::Law { span },
                        },
                        arguments,
                        support.clone(),
                        scope.clone(),
                    )?)
                } else {
                    None
                };
                let residual =
                    if *op == BinOp::Eq && numeric::is_numeric_type(input_ty, self.control)? {
                        if let Some((l, r)) = comparison {
                            Some(self.value(
                                numeric::binary(
                                    BinOp::Sub,
                                    self.graph.scalar(l)?,
                                    self.graph.scalar(r)?,
                                    self.control,
                                )?,
                                Rule::Construction("evaluation"),
                                vec![l, r],
                                support,
                                scope,
                            )?)
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                self.finish(
                    span,
                    ty,
                    value,
                    vec![left, right],
                    vec![],
                    None,
                    comparison,
                    residual,
                )
            }
            ExprKind::Call { args, .. } if self.environment.named_view(id)?.is_some() => {
                self.call(id, args, span, ty)
            }
            ExprKind::Tuple(_)
            | ExprKind::ListLit { .. }
            | ExprKind::SetLit { .. }
            | ExprKind::None(_)
            | ExprKind::Some(_)
            | ExprKind::Unit
            | ExprKind::Str(_)
            | ExprKind::Index { .. }
            | ExprKind::Call { .. } => self.composite(id, span, ty),
            _ => Err(self.unsupported(span, format!("式形 {:?}", expr.kind))),
        }
    }
    fn evaluated_reference(&self, reference: NodeRef) -> Result<Evaluated, Failure> {
        let node = self.graph.get(reference)?;
        let Some(Payload::Evaluation {
            expression, value, ..
        }) = &node.payload
        else {
            return Err(Failure::Internal("反復元がEvaluationでない".into()));
        };
        Ok(Evaluated {
            expression: *expression,
            evaluation: reference,
            value: *value,
            scope: node.scope.clone(),
            support: node.support.clone(),
            reasons: node.reasons.clone(),
            comparison: None,
            residual: None,
        })
    }
    fn quantification(&mut self, id: usize) -> Result<Evaluated, Failure> {
        let spec = super::quantifier::spec(self.environment.inputs.law(), id, self.control)?;
        let input = self.eval(spec.domain)?;
        let source = self
            .sources
            .get(&spec.span)
            .ok_or_else(|| Failure::Internal("量化元Sourceがない".into()))?
            .expression;
        let mut children = vec![input.clone()];
        let mut evidence = Vec::new();
        let mut results = Vec::new();
        let mut scope = input.scope.clone();
        let mut finite = None;
        if let Some(value) = input.value {
            let (Scalar::List { items, .. } | Scalar::Set { items, .. }) =
                self.graph.scalar(value)?
            else {
                return Err(Failure::Internal("量化域がList/Setでない".into()));
            };
            let Scalar::Set { ref items, .. } =
                data::set(spec.element.clone(), items, self.control)?
            else {
                unreachable!()
            };
            let mut elements = Vec::new();
            for item in items {
                #[cfg(test)]
                data::observe_actual(spec.span, self.graph.active, "quant_domain", elements.len());
                self.tick(Checkpoint::FiniteIteration)?;
                elements.push(self.value(
                    item.clone(),
                    Rule::Construction("domain"),
                    vec![source, input.evaluation],
                    input.support.clone(),
                    input.scope.clone(),
                )?);
                self.tick(Checkpoint::FiniteIteration)?;
            }
            let mut domain_scope = input.scope.clone();
            domain_scope.add_quantifier(spec.descriptor(None, Some(self.graph.active)));
            domain_scope.order_quantifiers_like(&self.graph.get(source)?.scope);
            let arguments = std::iter::once(source)
                .chain([input.evaluation])
                .chain(elements.iter().copied())
                .collect();
            let domain = self.push(Node {
                ty: NodeType::Domain,
                payload: Some(Payload::Domain {
                    ty: spec.element.clone(),
                    elements,
                }),
                rule: Rule::Construction("domain"),
                arguments,
                support: input.support.clone(),
                evidence: vec![],
                judgment: None,
                scope: domain_scope,
                reasons: vec![],
            })?;
            finite = Some(domain);
            scope.add_quantifier(spec.descriptor(finite, Some(self.graph.active)));
            scope.order_quantifiers_like(&self.graph.get(source)?.scope);
            for item in items {
                #[cfg(test)]
                let position = results.len();
                #[cfg(test)]
                data::observe_actual(spec.span, self.graph.active, "quant_body", position);
                self.tick(Checkpoint::FiniteIteration)?;
                let caller = self.graph.active;
                let index = self.graph.iterations.len();
                self.graph.iterations.push(super::call::Iteration {
                    caller,
                    source,
                    domain: input.evaluation,
                    member: super::call::Member::SetElement(item.clone()),
                    finite,
                });
                let old_sources = std::mem::take(&mut self.sources);
                let old_completed = std::mem::take(&mut self.completed);
                let old_lexical = self.lexical.clone();
                let old_base = std::mem::replace(&mut self.base, scope.clone());
                self.graph.active = super::call::Context {
                    iteration: Some(index),
                    ..caller
                };
                let evaluated = (|| -> Result<Evaluated, Failure> {
                    let body = self.eval(spec.body)?;
                    if spec.kind == crate::law::ast::QuantKind::Forall
                        && self.graph.boolean(body.value)? == Some(false)
                    {
                        #[cfg(test)]
                        data::observe_actual(
                            spec.span,
                            self.graph.active,
                            "quant_counterexample",
                            position,
                        );
                        self.tick(Checkpoint::FiniteIteration)?;
                        let arguments = vec![source, domain, body.evaluation];
                        let right = self.value(
                            Scalar::Bool(true),
                            Rule::Construction("evidence"),
                            arguments.clone(),
                            vec![],
                            body.scope.clone(),
                        )?;
                        let bindings = self
                            .environment
                            .quant_bindings(self.graph, self.graph.active)?;
                        let mut counter_support = input.support.clone();
                        counter_support.extend(body.support.iter().cloned());
                        counter_support.sort();
                        counter_support.dedup();
                        evidence.push(self.push(Node {
                            ty: NodeType::Evidence,
                            payload: Some(Payload::Counterexample {
                                bindings,
                                left: body.value.expect("falsebody"),
                                right,
                                facts: counter_support.clone(),
                            }),
                            rule: Rule::Construction("evidence"),
                            arguments,
                            support: counter_support,
                            evidence: vec![],
                            judgment: None,
                            scope: body.scope.clone(),
                            reasons: vec![],
                        })?);
                    }
                    Ok(body)
                })();
                self.graph.active = caller;
                self.sources = old_sources;
                self.completed = old_completed;
                self.lexical = old_lexical;
                self.base = old_base;
                let body = evaluated?;
                results.push(self.graph.boolean(body.value)?);
                children.push(body);
                self.tick(Checkpoint::FiniteIteration)?;
            }
        } else {
            scope.add_quantifier(spec.descriptor(None, Some(self.graph.active)));
            scope.order_quantifiers_like(&self.graph.get(source)?.scope);
        }
        let known = if finite.is_some() {
            super::quantifier::reduce(spec.kind, &results, self.control)?
        } else {
            None
        };
        let mut support = Vec::new();
        for child in &children {
            self.tick(Checkpoint::FiniteIteration)?;
            scope.merge(&child.scope);
            support.extend(child.support.iter().cloned());
        }
        support.sort();
        support.dedup();
        if matches!(
            (spec.kind, known),
            (crate::law::ast::QuantKind::Forall, Some(true))
                | (crate::law::ast::QuantKind::Exists, Some(false))
        ) {
            let domain = finite.expect("既知量化域");
            let mut instances = Vec::new();
            #[cfg(test)]
            data::observe_actual(spec.span, self.graph.active, "quant_exhaustion", 0);
            self.tick(Checkpoint::FiniteIteration)?;
            for body in &children[1..] {
                #[cfg(test)]
                data::observe_actual(
                    spec.span,
                    self.graph.active,
                    "quant_exhaustion",
                    instances.len() + 1,
                );
                self.tick(Checkpoint::FiniteIteration)?;
                instances.push(body.evaluation);
                self.tick(Checkpoint::FiniteIteration)?;
            }
            let arguments = std::iter::once(source)
                .chain([domain])
                .chain(instances.iter().copied())
                .collect();
            evidence.push(self.push(Node {
                ty: NodeType::Evidence,
                payload: Some(Payload::FiniteExhaustion {
                    domain,
                    checked: instances.len(),
                    instances,
                }),
                rule: Rule::Construction("evidence"),
                arguments,
                support: support.clone(),
                evidence: vec![],
                judgment: None,
                scope: scope.clone(),
                reasons: vec![],
            })?);
        }
        let value = if let Some(known) = known {
            Some(self.push(Node {
                ty: NodeType::Value(Type::Bool),
                payload: Some(Payload::Scalar(Scalar::Bool(known))),
                rule: Rule::Input {
                    kind: "law",
                    location: Location::Law { span: spec.span },
                },
                arguments: children.iter().map(|c| c.evaluation).collect(),
                support,
                evidence,
                judgment: None,
                scope,
                reasons: vec![],
            })?)
        } else {
            None
        };
        self.finish(
            spec.span,
            Type::Bool,
            value,
            children,
            vec![],
            None,
            None,
            None,
        )
    }
    fn comprehension(
        &mut self,
        domain: usize,
        elem: usize,
        filter: Option<usize>,
        span: (usize, usize),
        ty: Type,
    ) -> Result<Evaluated, Failure> {
        let input = self.eval(domain)?;
        let source = self
            .sources
            .get(&span)
            .ok_or_else(|| Failure::Internal("内包元Sourceがない".into()))?
            .expression;
        let mut children = vec![input.clone()];
        let Some(value) = input.value else {
            return self.lexical_result(span, ty, None, children);
        };
        let container = self.graph.scalar(value)?.clone();
        let (members, is_list) = match &container {
            Scalar::List { items, .. } => (items, true),
            Scalar::Set { items, .. } => (items, false),
            _ => return Err(Failure::Internal("内包域がList/Setでない".into())),
        };
        let mut values = Vec::new();
        let mut known = true;
        for (position, member) in members.iter().enumerate() {
            #[cfg(test)]
            data::observe_actual(span, self.graph.active, "comprehension_iteration", position);
            self.tick(Checkpoint::FiniteIteration)?;
            let caller = self.graph.active;
            let index = self.graph.iterations.len();
            self.graph.iterations.push(super::call::Iteration {
                caller,
                source,
                domain: input.evaluation,
                finite: None,
                member: if is_list {
                    super::call::Member::ListPosition(position)
                } else {
                    super::call::Member::SetElement(member.clone())
                },
            });
            let old_sources = std::mem::take(&mut self.sources);
            let old_completed = std::mem::take(&mut self.completed);
            let old_base = std::mem::replace(&mut self.base, input.scope.clone());
            let old_lexical = self.lexical.clone();
            self.graph.active = super::call::Context {
                iteration: Some(index),
                ..caller
            };
            let result = (|| -> Result<(), Failure> {
                let condition = if let Some(filter) = filter {
                    let evaluated = self.eval(filter)?;
                    let condition = self.graph.boolean(evaluated.value)?;
                    children.push(evaluated);
                    condition
                } else {
                    Some(true)
                };
                match condition {
                    Some(true) => {
                        let evaluated = self.eval(elem)?;
                        if let Some(value) = evaluated.value {
                            values.push(self.graph.scalar(value)?.clone());
                        } else {
                            known = false;
                        }
                        children.push(evaluated);
                    }
                    Some(false) => {}
                    None => {
                        known = false;
                    }
                }
                Ok(())
            })();
            self.graph.active = caller;
            self.sources = old_sources;
            self.completed = old_completed;
            self.base = old_base;
            self.lexical = old_lexical;
            result?;
            self.tick(Checkpoint::FiniteIteration)?;
        }
        let Type::Set(element) = &ty else {
            return Err(Failure::Internal("内包結果型がSetでない".into()));
        };
        let value = if known {
            #[cfg(test)]
            let previous = data::evaluation_context(Some((span, self.graph.active)));
            let constructed = data::set((**element).clone(), &values, self.control);
            #[cfg(test)]
            data::evaluation_context(previous);
            Some(constructed?)
        } else {
            None
        };
        self.lexical_result(span, ty, value, children)
    }
    fn composite(
        &mut self,
        id: ExprId,
        span: (usize, usize),
        ty: Type,
    ) -> Result<Evaluated, Failure> {
        let children = self
            .environment
            .composite_children(id)?
            .ok_or_else(|| self.unsupported(span, "数値組・射影・rat 以外の構成"))?;
        let mut evaluated = Vec::new();
        let mut arguments = Vec::new();
        let mut values = Vec::new();
        let mut known = true;
        let mut scope = self.base.clone();
        let mut support = Vec::new();
        for child in children {
            self.tick(Checkpoint::FiniteIteration)?;
            let child = self.eval(child)?;
            scope.merge(&child.scope);
            support.extend(child.support.iter().cloned());
            if let Some(value) = child.value {
                arguments.push(value);
                values.push(self.graph.scalar(value)?.clone());
            } else {
                known = false;
            }
            evaluated.push(child);
            self.tick(Checkpoint::FiniteIteration)?;
        }
        support.sort();
        support.dedup();
        let value = if known {
            #[cfg(test)]
            let previous = data::evaluation_context(Some((span, self.graph.active)));
            let constructed = self.environment.composite_value(id, &values);
            #[cfg(test)]
            data::evaluation_context(previous);
            Some(self.value(
                constructed?,
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                },
                arguments,
                support,
                scope,
            )?)
        } else {
            None
        };
        self.finish(span, ty, value, evaluated, vec![], None, None, None)
    }
    fn call(
        &mut self,
        id: ExprId,
        args: &[ExprId],
        span: (usize, usize),
        ty: Type,
    ) -> Result<Evaluated, Failure> {
        let declaration = self
            .environment
            .named_view(id)?
            .ok_or_else(|| Failure::Internal("named view targetがない".into()))?;
        let Signature::View { params, body, .. } = &declaration.signature else {
            unreachable!()
        };
        let mut arguments = Vec::new();
        for &arg in args {
            self.tick(Checkpoint::FiniteIteration)?;
            arguments.push(self.eval(arg)?);
        }
        let source = self
            .sources
            .get(&span)
            .ok_or_else(|| Failure::Internal("call Sourceがない".into()))?
            .clone();
        let caller = self.graph.active;
        let frame = self.graph.frames.len();
        self.graph.frames.push(super::call::Frame {
            caller,
            source: source.expression,
            arguments: arguments.iter().map(|a| a.evaluation).collect(),
        });
        let old_bindings = std::mem::take(&mut self.bindings);
        let old_formal = std::mem::take(&mut self.formal);
        let old_lexical = std::mem::take(&mut self.lexical);
        let old_sources = std::mem::take(&mut self.sources);
        let old_completed = std::mem::take(&mut self.completed);
        let old_base = std::mem::replace(&mut self.base, source.scope.clone());
        self.base.readings.insert(declaration.reading.clone());
        let old_declaration = std::mem::replace(&mut self.declaration, declaration);
        self.graph.active = super::call::Context {
            request: caller.request,
            frame: Some(frame),
            iteration: None,
        };
        for (parameter, argument) in params.iter().zip(&arguments) {
            self.formal.insert(parameter.name.clone(), argument.clone());
            if let Some(value) = argument.value {
                self.bindings.push(Binding {
                    name: parameter.name.clone(),
                    ty: parameter.ty.erase(),
                    value,
                });
            }
        }
        let result = self.eval(*body);
        self.graph.active = caller;
        self.bindings = old_bindings;
        self.formal = old_formal;
        self.lexical = old_lexical;
        self.sources = old_sources;
        self.completed = old_completed;
        self.base = old_base;
        self.declaration = old_declaration;
        let body = result?;
        self.tick(Checkpoint::FiniteIteration)?;
        let known = body
            .value
            .map(|v| self.graph.scalar(v).cloned())
            .transpose()?;
        arguments.push(body);
        self.lexical_result(span, ty, known, arguments)
    }
    // let/if の新しい値は元の子 Evaluation から構成する。値がない子も保持し、
    // その Evaluation を通常 Scalar として消費しない。
    fn lexical_result(
        &mut self,
        span: (usize, usize),
        ty: Type,
        known: Option<Scalar>,
        children: Vec<Evaluated>,
    ) -> Result<Evaluated, Failure> {
        let mut scope = self.base.clone();
        let mut support = Vec::new();
        let mut arguments = Vec::new();
        for child in &children {
            self.tick(Checkpoint::FiniteIteration)?;
            scope.merge(&child.scope);
            support.extend(child.support.iter().cloned());
            arguments.push(child.evaluation);
            self.tick(Checkpoint::FiniteIteration)?;
        }
        support.sort();
        support.dedup();
        let value = if let Some(known) = known {
            Some(self.value(
                known,
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                },
                arguments,
                support,
                scope,
            )?)
        } else {
            None
        };
        self.finish(span, ty, value, children, vec![], None, None, None)
    }
    fn field(
        &mut self,
        base: Evaluated,
        name: &str,
        span: (usize, usize),
    ) -> Result<Evaluated, Failure> {
        let Some(reference) = base.value else {
            return Err(self.unsupported(span, "未確定の参照からの field 読取り"));
        };
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = self.graph.scalar(reference)?
        else {
            return Err(self.unsupported(span, "原始 Ref 以外の field 読取り"));
        };
        let (snapshot, subject, entity) = (snapshot.clone(), subject.clone(), entity.clone());
        let s = self.environment.subject(&snapshot, &subject)?;
        if s.ty != entity {
            return Err(Failure::Internal("field owner 型が合わない".into()));
        }
        let fullname = format!("{entity}.{name}");
        let field = self.environment.field(&s.snapshot, &s.id, &fullname)?;
        if !matches!(field.ty, Type::Bool | Type::Ref(_) | Type::Owned(_, _))
            && !data::supported(&field.ty, self.environment.inputs.law(), self.control)?
        {
            return Err(self.unsupported(span, "Z/Bool/Ref 以外の原始 slot 評価"));
        }
        let fact = Fact {
            snapshot,
            subject,
            field: Some(fullname),
            atom: None,
        };
        match &field.slot {
            Slot::Known {
                atom,
                origin,
                value,
                pointer,
            } => {
                let value = scalar_from(
                    value,
                    &field.ty,
                    self.environment.inputs.law(),
                    self.control,
                )?
                .ok_or_else(|| self.unsupported(span, "Z/Bool/Ref 以外の原始値読取り"))?;
                let mut fact = fact;
                fact.atom = Some(atom.clone());
                let mut scope = self.base.clone();
                scope.merge(
                    &self
                        .environment
                        .scope(s, &self.declaration.reading, Some(origin))?,
                );
                let r = self.value(
                    value,
                    Rule::Input {
                        kind: "atom",
                        location: Location::ArchMap {
                            pointer: pointer.clone(),
                            span: None,
                        },
                    },
                    vec![reference],
                    vec![fact.clone()],
                    scope,
                )?;
                self.finish(
                    span,
                    field.ty.erase(),
                    Some(r),
                    vec![base],
                    vec![fact],
                    None,
                    None,
                    None,
                )
            }
            Slot::Missing => self.finish(
                span,
                field.ty.erase(),
                None,
                vec![base],
                vec![],
                Some(fact),
                None,
                None,
            ),
        }
    }
    fn transform_expression(
        &mut self,
        operation: TransformOp,
        operands: Vec<NodeRef>,
        scope: Scope,
    ) -> Result<NodeRef, Failure> {
        let mut arguments = Vec::new();
        for &operand in &operands {
            self.tick(Checkpoint::FiniteIteration)?;
            arguments.push(operand);
            self.tick(Checkpoint::FiniteIteration)?;
        }
        for binding in &self.bindings {
            self.control.checkpoint(Checkpoint::FiniteIteration)?;
            arguments.push(binding.value);
            self.control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        self.push(Node {
            ty: NodeType::Expression(Type::Bool),
            payload: Some(Payload::Transform {
                operation,
                operands,
                bindings: self.bindings.clone(),
            }),
            rule: Rule::Construction("expression"),
            arguments,
            support: vec![],
            evidence: vec![],
            judgment: None,
            scope,
            reasons: vec![],
        })
    }
    // 原 guard/body の Source を native not/and で結ぶ。架空の AST span は作らない。
    fn conditional_expression(
        &mut self,
        guard: &Evaluated,
        body: &Evaluated,
        scope: &Scope,
    ) -> Result<NodeRef, Failure> {
        let not_body =
            self.transform_expression(TransformOp::Not, vec![body.expression], body.scope.clone())?;
        let violation = self.transform_expression(
            TransformOp::And,
            vec![guard.expression, not_body],
            scope.clone(),
        )?;
        self.transform_expression(TransformOp::Not, vec![violation], scope.clone())
    }
    fn push_law_evaluation(&mut self, node: Node) -> Result<NodeRef, Failure> {
        self.environment.validate(self.graph, &node)?;
        let scope = node.scope.clone();
        let retained = &mut self.retained_scope;
        let completed = &mut self.answer_evaluation;
        // 検査済みの適用評価を append と同時に保持し、post 停止でも生 body に戻さない。
        Ok(self.graph.push_with_metadata(node, |reference| {
            retained.merge(&scope);
            *completed = Some(reference);
        })?)
    }
    fn answer(
        &mut self,
        params: &[Param],
        guard: Option<ExprId>,
        body: ExprId,
        role: Option<Role>,
    ) -> Result<Answer, Failure> {
        self.bind(params)?;
        let guard_id = guard;
        let body_id = body;
        let guard = guard.map(|g| self.eval(g)).transpose()?;
        let body = self.eval(body)?;
        let mut scope = body.scope.clone();
        if let Some(g) = &guard {
            scope.merge(&g.scope);
        }
        let mut support = body.support.clone();
        if let Some(g) = &guard {
            self.tick(Checkpoint::FiniteIteration)?;
            support.extend(g.support.iter().cloned());
            self.tick(Checkpoint::FiniteIteration)?;
        }
        support.sort();
        support.dedup();
        let mut reasons = body.reasons.clone();
        if let Some(g) = &guard {
            reasons.extend(g.reasons.iter().cloned());
        }
        sort_reasons(&mut reasons);
        let mut answer = Answer {
            id: self.request.id.clone(),
            status: Decision::Undetermined,
            outputs: BTreeMap::from([("evaluation".into(), body.evaluation)]),
            claim: None,
            evidence: vec![],
            reasons: reasons.clone(),
            scope: scope.clone(),
        };
        if self.request.kind == QuestionKind::Evaluate {
            if let Some(value) = body.value {
                answer.outputs.insert("value".into(), value);
                answer.status = Decision::Established;
            }
            return Ok(answer);
        }
        let instance = self.push(Node {
            ty: NodeType::LawInstance,
            payload: Some(Payload::LawInstance {
                name: self.declaration.name.clone(),
                role: match role.ok_or_else(|| Failure::Internal("Law role がない".into()))? {
                    Role::Required => "required",
                    Role::Optional => "optional",
                },
                bindings: self.bindings.clone(),
                guard: guard.as_ref().map(|g| g.expression),
                body: body.expression,
                occurrence: Location::Law {
                    span: self.declaration.span,
                },
            }),
            rule: Rule::Construction("law_instance"),
            arguments: std::iter::once(body.evaluation)
                .chain(guard.as_ref().map(|g| g.evaluation))
                .chain(self.bindings.iter().map(|b| b.value))
                .collect(),
            support: support.clone(),
            evidence: vec![],
            judgment: None,
            scope: scope.clone(),
            reasons: vec![],
        })?;
        // raw body の値と、guard による条件付き Law の値を区別する。
        let guard_value = guard
            .as_ref()
            .map(|g| self.graph.boolean(g.value))
            .transpose()?;
        let conditional = guard_value.is_some_and(|g| g != Some(true));
        let (law_expression, law_value) = if conditional {
            self.tick(Checkpoint::Expression)?;
            let g = guard.as_ref().expect("明示 guard");
            let expression = self.conditional_expression(g, &body, &scope)?;
            let value = conditional_bool(guard_value.flatten(), self.graph.boolean(body.value)?)
                .map(|value| {
                    self.value(
                        Scalar::Bool(value),
                        Rule::Construction("evaluation"),
                        vec![instance, expression],
                        support.clone(),
                        scope.clone(),
                    )
                })
                .transpose()?;
            self.tick(Checkpoint::Expression)?;
            (expression, value)
        } else {
            (body.expression, body.value)
        };
        let applicability = match guard_value {
            None | Some(Some(true)) => "applicable",
            Some(Some(false)) => "not_applicable",
            Some(None) => "undetermined",
        };
        // 明示 guard の適用評価。parts は値を上書きせず元 guard/body を保持する。
        let evaluation = if let Some(g) = &guard {
            self.push_law_evaluation(Node {
                ty: NodeType::Evaluation(Type::Bool),
                payload: Some(Payload::Evaluation {
                    expression: law_expression,
                    bindings: self.bindings.clone(),
                    parts: vec![
                        Part {
                            location: Location::Law {
                                span: self.environment.inputs.law().exprs
                                    [guard_id.expect("明示 guard")]
                                .span,
                            },
                            value: g.value,
                            residual: g.residual,
                            children: vec![g.evaluation],
                        },
                        Part {
                            location: Location::Law {
                                span: self.environment.inputs.law().exprs[body_id].span,
                            },
                            value: body.value,
                            residual: body.residual,
                            children: vec![body.evaluation],
                        },
                    ],
                    value: law_value,
                    applicability,
                }),
                rule: Rule::Construction("evaluation"),
                arguments: vec![instance, body.evaluation, g.evaluation],
                support: support.clone(),
                evidence: vec![],
                judgment: None,
                scope: scope.clone(),
                reasons: reasons.clone(),
            })?
        } else {
            body.evaluation
        };
        answer.outputs.insert("evaluation".into(), evaluation);
        self.answer_evaluation = Some(evaluation);
        let decision = match law_value.map(|r| self.graph.scalar(r)).transpose()? {
            Some(Scalar::Bool(true)) => Decision::Established,
            Some(Scalar::Bool(false)) => Decision::Refuted,
            None => Decision::Undetermined,
            _ => return Err(Failure::Internal("Law body が Bool でない".into())),
        };
        let mut evidence = Vec::new();
        if let Some(value) = law_value {
            let (left, right) = match body.comparison.filter(|_| !conditional) {
                Some(pair) => pair,
                None => (
                    value,
                    self.value(
                        Scalar::Bool(true),
                        Rule::Construction("proposition"),
                        vec![instance],
                        vec![],
                        scope.clone(),
                    )?,
                ),
            };
            let e = self.push(Node {
                ty: NodeType::Evidence,
                payload: Some(Payload::EvaluationEvidence {
                    instance,
                    lhs: left,
                    rhs: right,
                    residual: if conditional { None } else { body.residual },
                }),
                rule: Rule::Construction("evidence"),
                arguments: vec![instance, evaluation],
                support: support.clone(),
                evidence: vec![],
                judgment: None,
                scope: scope.clone(),
                reasons: vec![],
            })?;
            evidence.push(e);
            if decision == Decision::Refuted {
                for index in 0..self.graph.nodes.len() {
                    self.tick(Checkpoint::FiniteIteration)?;
                    let reference = NodeRef(index);
                    if matches!(
                        &self.graph.nodes[index].payload,
                        Some(Payload::Counterexample { .. })
                    ) && self
                        .graph
                        .evaluation_evidence_contains(evaluation, reference)?
                    {
                        evidence.push(reference);
                    }
                }
                let e = self.push(Node {
                    ty: NodeType::Evidence,
                    payload: Some(Payload::Counterexample {
                        bindings: self.bindings.clone(),
                        left,
                        right,
                        facts: support.clone(),
                    }),
                    rule: Rule::Construction("evidence"),
                    arguments: vec![instance, evaluation],
                    support: support.clone(),
                    evidence: vec![],
                    judgment: None,
                    scope: scope.clone(),
                    reasons: vec![],
                })?;
                evidence.push(e);
            }
        }
        let proposition = self.push(Node {
            ty: NodeType::Proposition,
            payload: Some(Payload::Proposition { instance }),
            rule: Rule::Construction("proposition"),
            arguments: vec![instance, evaluation],
            support,
            evidence: evidence.clone(),
            judgment: Some(Judgment {
                status: decision,
                evidence: evidence.clone(),
                reasons: reasons.clone(),
            }),
            scope,
            reasons,
        })?;
        answer.outputs.insert("proposition".into(), proposition);
        answer.claim = Some(proposition);
        answer.status = decision;
        answer.evidence = evidence;
        Ok(answer)
    }
}

pub fn evaluate_observed(
    prepared: PreparedObserved,
    control: &mut Control,
) -> Result<ObservedEvaluation, EvaluationFailure> {
    evaluate_observed_with_validator(prepared, control, |environment, graph, request, answer| {
        environment.validate_answer(graph, request, answer)
    })
}

fn evaluate_observed_with_validator(
    prepared: PreparedObserved,
    control: &mut Control,
    mut validate_answer: impl FnMut(
        &Environment<'_>,
        &Graph,
        &Request,
        &Answer,
    ) -> Result<(), ValidationFailure>,
) -> Result<ObservedEvaluation, EvaluationFailure> {
    let mut graph = Graph::new(control);
    graph.requests = prepared.requests().requests().to_vec();
    let mut answers: Vec<Option<Answer>> = vec![None; prepared.requests().requests().len()];
    let mut issues = Vec::new();
    let mut internal = false;
    {
        let environment = Environment::new(prepared.inputs(), control).ok();
        for &index in prepared.requests().evaluation_order() {
            let request = &prepared.requests().requests()[index];
            let declaration = &prepared.inputs().law().declarations[request.declaration()];
            let mut base = Scope::default();
            base.readings.insert(declaration.reading.clone());
            let stop = control.stop_reason();
            if let Some(reason) = stop {
                let reason = Reason::stopped(&request.id, reason);
                issues.push(reason.clone());
                answers[index] = Some(Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons: vec![reason],
                    scope: base,
                });
                continue;
            }
            if internal {
                let reason = Reason::internal(&request.id, "先行導出の内部照合失敗".into());
                issues.push(reason.clone());
                answers[index] = Some(Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons: vec![reason],
                    scope: base,
                });
                continue;
            }
            let environment = environment.as_ref().expect("停止しない環境構築は完成する");
            graph.active = super::call::Context {
                request: index,
                frame: None,
                iteration: None,
            };
            let mut evaluator = Evaluator {
                environment,
                graph: &mut graph,
                control,
                request,
                declaration,
                bindings: vec![],
                lexical: BTreeMap::new(),
                formal: BTreeMap::new(),
                base: base.clone(),
                retained_scope: Scope::default(),
                reasons: vec![],
                completed: BTreeMap::new(),
                answer_evaluation: None,
                sources: BTreeMap::new(),
            };
            let (params, guard, body, role) = match &declaration.signature {
                Signature::View { params, body, .. } => (params, None, *body, None),
                Signature::Law {
                    params,
                    guard,
                    body,
                    role,
                } => (params, *guard, *body, Some(*role)),
                _ => unreachable!("要求解決済みの view/Law"),
            };
            let result = (|| {
                evaluator.tick(Checkpoint::FiniteIteration)?;
                evaluator.answer(params, guard, body, role)
            })();
            // Answer の検査は意味導出の完了前に行い、post 停止で完成済み Answer を捨てない。
            let result = result.and_then(|a| {
                validate_answer(evaluator.environment, evaluator.graph, request, &a)?;
                Ok(a)
            });
            match result {
                Ok(answer) => {
                    issues.extend(answer.reasons.iter().cloned());
                    answers[index] = Some(answer);
                    if let Err(reason) = evaluator.tick(Checkpoint::FiniteIteration) {
                        let Failure::Stop(reason) = reason else {
                            unreachable!()
                        };
                        issues.push(Reason::stopped(&request.id, reason));
                    }
                }
                Err(Failure::NotImplemented { location, feature }) => {
                    return Err(EvaluationFailure::NotImplemented {
                        declaration: declaration.name.clone(),
                        location,
                        feature,
                    });
                }
                Err(failure) => {
                    let reason = match failure {
                        Failure::Stop(reason) => Reason::stopped(&request.id, reason),
                        Failure::Internal(operation) => {
                            internal = true;
                            Reason::internal(&request.id, operation)
                        }
                        _ => unreachable!(),
                    };
                    let mut reasons = evaluator.reasons.clone();
                    reasons.push(reason);
                    sort_reasons(&mut reasons);
                    let mut outputs = BTreeMap::new();
                    let mut scope = evaluator.base.clone();
                    // root が未完成でも、保持済みの依存式・値の範囲と由来を残す。
                    scope.merge(&evaluator.retained_scope);
                    // 集約済みの適用評価も、後続の証拠構成が停止した際に保持する。
                    if let Some(evaluation) = evaluator.answer_evaluation {
                        outputs.insert("evaluation".into(), evaluation);
                    }
                    // 明示 guard の適用集約が未完成なら生 body を回答へ昇格しない。
                    if let Some(completed) = evaluator.completed.get(&body)
                        && (request.kind == QuestionKind::Evaluate || guard.is_none())
                    {
                        outputs.insert("evaluation".into(), completed.evaluation);
                        scope.merge(&completed.scope);
                        if request.kind == QuestionKind::Evaluate
                            && let Some(v) = completed.value
                        {
                            outputs.insert("value".into(), v);
                        }
                    }
                    issues.extend(reasons.iter().cloned());
                    answers[index] = Some(Answer {
                        id: request.id.clone(),
                        status: Decision::Undetermined,
                        outputs,
                        claim: None,
                        evidence: vec![],
                        reasons,
                        scope,
                    });
                }
            }
        }
    }
    sort_reasons(&mut issues);
    let answers: Vec<_> = answers
        .into_iter()
        .map(|a| a.expect("依存順は全要求を含む"))
        .collect();
    let status = if matches!(control.stop_reason(), Some(StopReason::Cancelled(_))) {
        "interrupted"
    } else if internal {
        "error"
    } else if control.stop_reason().is_some() {
        "interrupted"
    } else if answers.iter().any(|a| a.status == Decision::Undetermined) {
        "partial"
    } else {
        "complete"
    };
    Ok(ObservedEvaluation {
        prepared,
        nodes: graph.nodes,
        #[cfg(test)]
        contexts: graph.contexts,
        #[cfg(test)]
        frames: graph.frames,
        #[cfg(test)]
        iterations: graph.iterations,
        answers,
        issues,
        status,
    })
}

#[cfg(test)]
mod recheck_tests {
    use super::*;
    use crate::canonical::Json;
    #[test]
    fn answer_identity_failure_reaches_driver_and_preserves_prior_results() {
        fn prepare(control: &mut Control) -> PreparedObserved {
            let law = include_str!("../../tests/fixtures/counter.law").replace(
                "view amount(s: State): Z = s.count;",
                "view amount(s: State): Z = s.count;\n  view later(s: State): Z = s.count + 137;",
            );
            prepare_observed(
                InputSources::from_bytes(
                    vec![include_bytes!("../../tests/fixtures/counter.atoms.json").to_vec()],
                    law.into_bytes(),
                    include_str!("../../tests/fixtures/counter.archmap.json")
                        .replace("\"value\": \"2\"", "\"value\": \"12\"")
                        .into_bytes(),
                ),
                &[
                    "amount=evaluate(CountCheck.amount,s=@v/s)",
                    "bounded=check(CountAudit.bounded,s=@v/s)",
                    "fault=check(CountCheck.nonnegative,s=@v/s)",
                    "later=evaluate(CountCheck.later,s=@v/s)",
                ],
                control,
            )
            .unwrap()
        }

        let mut normal_control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        let normal_prepared = prepare(&mut normal_control);
        let normal = evaluate_observed(normal_prepared, &mut normal_control).unwrap();
        assert_eq!(normal.status(), "complete");
        assert!(normal.issues.is_empty());
        assert_eq!(normal.answers[2].status, Decision::Established);
        assert!(normal.answers[2].claim.is_some());
        let mut normal_graph = Graph::default();
        normal_graph.nodes = normal.nodes.clone();
        assert_eq!(
            normal_graph
                .scalar(normal.answers[3].outputs["value"])
                .unwrap(),
            &Scalar::Z(149.into())
        );

        let mut control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        let prepared = prepare(&mut control);
        let Signature::View { body: later, .. } =
            &prepared.inputs().law().declarations["CountCheck.later"].signature
        else {
            unreachable!()
        };
        let later_span = prepared.inputs().law().exprs[*later].span;
        let mut validated = Vec::new();
        let mut nodes_at_failure = None;
        let mut original_failure = None;
        let result = evaluate_observed_with_validator(
            prepared,
            &mut control,
            |environment, graph, request, answer| {
                validated.push(request.id.clone());
                environment.validate_answer(graph, request, answer)?;
                if request.id != "fault" {
                    return Ok(());
                }
                assert_eq!(answer.status, Decision::Established);
                assert!(answer.claim.is_some());
                assert!(!answer.evidence.is_empty());
                let mut wrong = answer.clone();
                wrong.id = "different-request".into();
                nodes_at_failure = Some(graph.nodes.len());
                let failure = environment.validate_answer(graph, request, &wrong);
                let Err(ValidationFailure::Internal(operation)) = &failure else {
                    panic!("実validatorはAnswerの帰属不整合をInternalで拒否する")
                };
                original_failure = Some(operation.clone());
                failure
            },
        )
        .unwrap();
        assert_eq!(result.status(), "error");
        assert!(control.stop_reason().is_none());
        assert_eq!(validated, ["amount", "bounded", "fault"]);
        assert_eq!(Some(result.nodes.len()), nodes_at_failure);
        assert_eq!(
            original_failure.as_deref(),
            Some("Answer ID が元Requestと違う")
        );
        assert_eq!(result.answers.len(), 4);
        let mut graph = Graph::default();
        graph.nodes = result.nodes.clone();
        let amount = &result.answers[0];
        assert_eq!(amount.status, Decision::Established);
        assert!(amount.claim.is_none());
        assert!(amount.evidence.is_empty());
        assert_eq!(
            graph.get(amount.outputs["value"]).unwrap().ty,
            NodeType::Value(Type::Z)
        );
        assert_eq!(
            graph.scalar(amount.outputs["value"]).unwrap(),
            &Scalar::Z(12.into())
        );
        let count = Fact {
            snapshot: "v".into(),
            subject: "s".into(),
            field: Some("Counter.State.count".into()),
            atom: Some("count".into()),
        };
        assert!(
            graph
                .get(amount.outputs["evaluation"])
                .unwrap()
                .support
                .contains(&count)
        );
        let bounded = &result.answers[1];
        assert_eq!(bounded.status, Decision::Refuted);
        let claim = graph.get(bounded.claim.unwrap()).unwrap();
        assert_eq!(claim.ty, NodeType::Proposition);
        let judgment = claim.judgment.as_ref().unwrap();
        assert_eq!(judgment.status, Decision::Refuted);
        assert_eq!(judgment.evidence, bounded.evidence);
        assert!(claim.support.contains(&count));
        let counterexample = bounded
            .evidence
            .iter()
            .find_map(|r| {
                let node = graph.get(*r).unwrap();
                if let Some(Payload::Counterexample {
                    bindings,
                    left,
                    right,
                    facts,
                }) = &node.payload
                {
                    Some((node, bindings, left, right, facts))
                } else {
                    None
                }
            })
            .expect("先行Lawの元反例を保持する");
        let (node, bindings, left, right, facts) = counterexample;
        assert_eq!(graph.scalar(*left).unwrap(), &Scalar::Z(12.into()));
        assert_eq!(graph.scalar(*right).unwrap(), &Scalar::Z(10.into()));
        assert!(node.support.contains(&count));
        assert!(facts.contains(&count));
        assert_eq!(bindings[0].name, "s");
        assert_eq!(
            graph.scalar(bindings[0].value).unwrap(),
            &Scalar::Subject {
                snapshot: "v".into(),
                subject: "s".into(),
                entity: "Counter.State".into(),
            }
        );
        assert!(result.nodes.iter().any(|node| {
            node.support.contains(&count)
                && matches!(&node.rule,
                Rule::Input { kind: "atom", location: Location::ArchMap { pointer, .. } }
                if pointer == "/snapshots/0/atoms/0/value")
        }));
        let Json::Obj(ref normal_wire) = normal.wire() else {
            unreachable!()
        };
        let Json::Obj(ref failed_wire) = result.wire() else {
            unreachable!()
        };
        let (Json::Arr(normal_answers), Json::Arr(failed_answers)) =
            (&normal_wire["answers"], &failed_wire["answers"])
        else {
            unreachable!()
        };
        assert_eq!(&failed_answers[..2], &normal_answers[..2]);
        let (Json::Arr(normal_nodes), Json::Arr(failed_nodes)) =
            (&normal_wire["nodes"], &failed_wire["nodes"])
        else {
            unreachable!()
        };
        assert_eq!(failed_nodes, &normal_nodes[..failed_nodes.len()]);
        for (index, operation) in [
            (2, "Answer ID が元Requestと違う"),
            (3, "先行導出の内部照合失敗"),
        ] {
            let answer = &result.answers[index];
            assert_eq!(answer.status, Decision::Undetermined);
            assert!(answer.claim.is_none());
            assert!(answer.evidence.is_empty());
            assert!(!answer.outputs.contains_key("proposition"));
            assert_eq!(answer.reasons.len(), 1);
            let reason = &answer.reasons[0];
            assert!(matches!(&reason.kind, ReasonKind::Internal(value) if value == operation));
            assert_eq!(reason.request, answer.id);
            assert!(reason.location.is_none());
            assert!(
                result
                    .issues
                    .iter()
                    .any(|issue| issue.wire() == reason.wire())
            );
        }
        assert_eq!(result.issues.len(), 2);
        assert!(result.answers[2].outputs.contains_key("evaluation"));
        assert!(result.answers[3].outputs.is_empty());
        assert!(result.nodes.iter().all(|node| !matches!(&node.rule,
            Rule::Input { location: Location::Law { span }, .. }
            if later_span.0 <= span.0 && span.1 <= later_span.1
        )));
        assert!(result.nodes.iter().all(|node| !matches!(&node.payload,
            Some(Payload::Scalar(Scalar::Z(value))) if *value == 149.into()
        )));
    }

    fn value_examples(missing: bool) -> ObservedEvaluation {
        let law = include_str!("../../tests/fixtures/counter.law").replace(
            "view amount(s: State): Z = s.count;",
            "view amount(s: State): Z = s.count;\n  view zero(s: State): Z = 0;\n  view yes(s: State): Bool = true;\n  view no(s: State): Bool = false;\n  view negative(s: State): Z = -s.count;\n  view same(s: State): Bool = s.count = 10;\n  view sameBool(s: State): Bool = true = false;",
        );
        let mut map = include_str!("../../tests/fixtures/counter.archmap.json").to_owned();
        if missing {
            map = map.replace(
                r#"{"id": "count", "subject": "s", "field": "Counter.State.count", "value": "2", "origin": "model"}"#,
                "",
            );
        }
        evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![include_bytes!("../../tests/fixtures/counter.atoms.json").to_vec()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &[
                "amount=evaluate(CountCheck.amount,s=@v/s)",
                "zero=evaluate(CountCheck.zero,s=@v/s)",
                "yes=evaluate(CountCheck.yes,s=@v/s)",
                "no=evaluate(CountCheck.no,s=@v/s)",
                "negative=evaluate(CountCheck.negative,s=@v/s)",
                "judgment=check(CountCheck.nonnegative,s=@v/s)",
                "same=evaluate(CountCheck.same,s=@v/s)",
                "sameBool=evaluate(CountCheck.sameBool,s=@v/s)",
            ],
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn rejects_literal_evaluation_value_substitution_and_omission() {
        let result = value_examples(false);
        assert_eq!(result.status(), "complete");
        let mut control = Control::unlimited();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let mut graph = Graph::new(&control);
        graph.nodes = result.nodes.clone();
        for (answer, replacement) in [(1, 0), (3, 2)] {
            let evaluation = result.answers[answer].outputs["evaluation"];
            let replacement = result.answers[replacement].outputs["value"];
            assert!(replacement.0 < evaluation.0, "差替え先は既出の正しい値");
            environment
                .validate(&graph, &graph.nodes[evaluation.0])
                .unwrap();
            for new_value in [Some(replacement), None] {
                let mut wrong = graph.nodes[evaluation.0].clone();
                let Some(Payload::Evaluation { value, parts, .. }) = &mut wrong.payload else {
                    unreachable!()
                };
                *value = new_value;
                parts[0].value = new_value;
                assert!(matches!(
                    environment.validate(&graph, &wrong),
                    Err(ValidationFailure::Internal(_))
                ));
            }
        }
    }
    #[test]
    fn rejects_negation_result_omission_and_wrong_value() {
        for missing in [false, true] {
            let result = value_examples(missing);
            assert_eq!(
                result.status(),
                if missing { "partial" } else { "complete" }
            );
            let mut control = Control::unlimited();
            let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
            let mut graph = Graph::new(&control);
            graph.nodes = result.nodes.clone();
            let evaluation = result.answers[4].outputs["evaluation"];
            let original = &graph.nodes[evaluation.0];
            environment.validate(&graph, original).unwrap();
            let Some(Payload::Evaluation { value, .. }) = &original.payload else {
                unreachable!()
            };
            if missing {
                assert!(value.is_none());
            } else {
                assert_eq!(
                    graph.scalar(value.unwrap()).unwrap(),
                    &Scalar::Z((-2).into())
                );
            }
            let zero = result.answers[1].outputs["value"];
            for new_value in [Some(zero), None] {
                if missing && new_value.is_none() {
                    continue;
                }
                let mut wrong = original.clone();
                let Some(Payload::Evaluation { value, parts, .. }) = &mut wrong.payload else {
                    unreachable!()
                };
                *value = new_value;
                parts[0].value = new_value;
                assert!(matches!(
                    environment.validate(&graph, &wrong),
                    Err(ValidationFailure::Internal(_))
                ));
            }
        }
    }
    #[test]
    fn rejects_answer_value_with_wrong_type_value_or_missing_evaluation() {
        let result = value_examples(false);
        let mut graph = Graph::default();
        graph.nodes = result.nodes.clone();
        let original = &result.answers[0];
        graph.validate_answer(original, false).unwrap();
        let subject = NodeRef(
            graph
                .nodes
                .iter()
                .position(|n| matches!(n.payload, Some(Payload::Scalar(Scalar::Subject { .. }))))
                .unwrap(),
        );
        for replacement in [subject, result.answers[1].outputs["value"]] {
            let mut wrong = original.clone();
            wrong.outputs.insert("value".into(), replacement);
            assert!(matches!(
                graph.validate_answer(&wrong, false),
                Err(ValidationFailure::Internal(_))
            ));
        }
        for removed in ["value", "evaluation"] {
            let mut wrong = original.clone();
            wrong.outputs.remove(removed);
            assert!(matches!(
                graph.validate_answer(&wrong, false),
                Err(ValidationFailure::Internal(_))
            ));
        }
        let mut wrong = original.clone();
        wrong
            .outputs
            .insert("evaluation".into(), result.answers[1].outputs["evaluation"]);
        assert!(matches!(
            graph.validate_answer(&wrong, false),
            Err(ValidationFailure::Internal(_))
        ));
    }
    #[test]
    fn rejects_answer_output_from_a_different_check_evaluation() {
        let result = value_examples(false);
        let mut graph = Graph::default();
        graph.nodes = result.nodes.clone();
        let original = &result.answers[5];
        graph.validate_answer(original, true).unwrap();
        let mut wrong = original.clone();
        wrong
            .outputs
            .insert("evaluation".into(), result.answers[2].outputs["evaluation"]);
        assert!(matches!(
            graph.validate_answer(&wrong, true),
            Err(ValidationFailure::Internal(_))
        ));
        let mut wrong = original.clone();
        wrong
            .outputs
            .insert("value".into(), result.answers[2].outputs["value"]);
        assert!(matches!(
            graph.validate_answer(&wrong, true),
            Err(ValidationFailure::Internal(_))
        ));
        let mut wrong = result.answers[2].clone();
        wrong.claim = original.claim;
        wrong
            .outputs
            .insert("proposition".into(), original.claim.unwrap());
        assert!(matches!(
            graph.validate_answer(&wrong, false),
            Err(ValidationFailure::Internal(_))
        ));
    }
    #[test]
    fn rejects_evidence_from_a_different_law_or_without_the_counterexample() {
        let result = example();
        let mut control = Control::unlimited();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let mut graph = Graph::new(&control);
        graph.nodes = result.nodes.clone();
        let original = graph.nodes[result.answers[0].claim.unwrap().0].clone();
        environment.validate(&graph, &original).unwrap();
        let foreign = result.answers[1].evidence[0];
        let evaluation_only = original
            .evidence
            .iter()
            .copied()
            .find(|r| {
                matches!(
                    graph.nodes[r.0].payload,
                    Some(Payload::EvaluationEvidence { .. })
                )
            })
            .unwrap();
        for evidence in [vec![foreign], vec![evaluation_only]] {
            let mut wrong = original.clone();
            wrong.evidence = evidence.clone();
            wrong.judgment.as_mut().unwrap().evidence = evidence;
            assert!(matches!(
                environment.validate(&graph, &wrong),
                Err(ValidationFailure::Internal(_))
            ));
            assert!(matches!(
                graph.push(wrong),
                Err(ValidationFailure::Internal(_))
            ));
        }
        let mut wrong = result.answers[0].clone();
        wrong.evidence = vec![foreign];
        assert!(matches!(
            graph.validate_answer(&wrong, true),
            Err(ValidationFailure::Internal(_))
        ));
        let mut wrong = original.clone();
        wrong.judgment.as_mut().unwrap().evidence = vec![foreign];
        assert!(matches!(
            environment.validate(&graph, &wrong),
            Err(ValidationFailure::Internal(_))
        ));
    }
    #[test]
    fn rejects_evaluation_scope_changed_with_its_source_and_answer() {
        let result = value_examples(false);
        let mut control = Control::unlimited();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let mut graph = Graph::new(&control);
        graph.nodes = result.nodes.clone();
        let reference = result.answers[0].outputs["evaluation"];
        let original = graph.nodes[reference.0].clone();
        environment.validate(&graph, &original).unwrap();
        for field in ["modes", "readings", "snapshots", "domain"] {
            graph.nodes = result.nodes.clone();
            let mut wrong = original.clone();
            match field {
                "modes" => wrong.scope.modes = ["observed".into()].into(),
                "readings" => wrong.scope.readings = ["CountAudit".into()].into(),
                "snapshots" => wrong.scope.snapshots = ["other".into()].into(),
                _ => wrong.scope.completions = true,
            }
            let Some(Payload::Evaluation { expression, .. }) = &wrong.payload else {
                unreachable!()
            };
            graph.nodes[expression.0].scope = wrong.scope.clone();
            let mut answer = result.answers[0].clone();
            answer.scope = wrong.scope.clone();
            graph.nodes[reference.0] = wrong.clone();
            graph.validate_answer(&answer, false).unwrap();
            // source/evaluation/answer の相互同値だけでは元入力の代用にならない。
            assert!(matches!(
                environment.validate(&graph, &wrong),
                Err(ValidationFailure::Internal(_))
            ));
        }
    }
    #[test]
    fn rejects_wrong_or_missing_integer_residual_and_residual_on_bool_equality() {
        let result = value_examples(false);
        let mut control = Control::unlimited();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let mut graph = Graph::new(&control);
        graph.nodes = result.nodes.clone();
        let original = &graph.nodes[result.answers[6].outputs["evaluation"].0];
        environment.validate(&graph, original).unwrap();
        let Some(Payload::Evaluation { parts, .. }) = &original.payload else {
            unreachable!()
        };
        assert_eq!(
            graph.scalar(parts[0].residual.unwrap()).unwrap(),
            &Scalar::Z((-8).into())
        );
        for residual in [Some(result.answers[0].outputs["value"]), None] {
            let mut wrong = original.clone();
            let Some(Payload::Evaluation { parts, .. }) = &mut wrong.payload else {
                unreachable!()
            };
            parts[0].residual = residual;
            assert!(matches!(
                environment.validate(&graph, &wrong),
                Err(ValidationFailure::Internal(_))
            ));
        }
        let mut wrong = graph.nodes[result.answers[7].outputs["evaluation"].0].clone();
        let Some(Payload::Evaluation { parts, .. }) = &mut wrong.payload else {
            unreachable!()
        };
        assert!(parts[0].residual.is_none());
        parts[0].residual = Some(result.answers[0].outputs["value"]);
        assert!(matches!(
            environment.validate(&graph, &wrong),
            Err(ValidationFailure::Internal(_))
        ));
    }
    fn example() -> ObservedEvaluation {
        let sources = InputSources::from_bytes(
            vec![include_bytes!("../../tests/fixtures/counter.atoms.json").to_vec()],
            include_bytes!("../../tests/fixtures/counter.law").to_vec(),
            include_str!("../../tests/fixtures/counter.archmap.json")
                .replace("\"value\": \"2\"", "\"value\": \"12\"")
                .into_bytes(),
        );
        evaluate_observed_bytes(
            sources,
            &[
                "a=check(CountAudit.bounded,s=@v/s)",
                "b=check(CountCheck.nonnegative,s=@v/s)",
            ],
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn rejects_forged_arithmetic_and_wrong_counterexample_operands() {
        let result = example();
        assert_eq!(result.status(), "complete");
        let mut control = Control::unlimited();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let mut graph = Graph::new(&control);
        graph.nodes = result.nodes.clone();
        let mut arithmetic = graph
            .nodes
            .iter()
            .find(|n| matches!(&n.payload, Some(Payload::Scalar(Scalar::Bool(false)))))
            .unwrap()
            .clone();
        arithmetic.payload = Some(Payload::Scalar(Scalar::Bool(true)));
        assert!(matches!(
            environment.validate(&graph, &arithmetic),
            Err(ValidationFailure::Internal(_))
        ));
        let zero = NodeRef(
            graph
                .nodes
                .iter()
                .position(
                    |n| matches!(&n.payload,Some(Payload::Scalar(Scalar::Z(n))) if n==&0.into()),
                )
                .unwrap(),
        );
        let mut counterexample = graph
            .nodes
            .iter()
            .find(|n| matches!(n.payload, Some(Payload::Counterexample { .. })))
            .unwrap()
            .clone();
        let Some(Payload::Counterexample { right, .. }) = &mut counterexample.payload else {
            unreachable!()
        };
        *right = zero;
        // 12 <= 0 も false だが、元 body の右辺 10 と違うため拒否する。
        assert!(matches!(
            environment.validate(&graph, &counterexample),
            Err(ValidationFailure::Internal(_))
        ));
    }
    #[test]
    fn rejects_wrong_ast_child_evaluation_and_binding_identity() {
        let result = example();
        let mut control = Control::unlimited();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let mut graph = Graph::new(&control);
        graph.nodes = result.nodes.clone();
        let mut evaluation=graph.nodes.iter().find(|n|matches!(&n.payload,Some(Payload::Evaluation{parts,..}) if parts[0].children.len()==2)).unwrap().clone();
        let Some(Payload::Evaluation { parts, .. }) = &mut evaluation.payload else {
            unreachable!()
        };
        parts[0].children.swap(0, 1);
        assert!(matches!(
            environment.validate(&graph, &evaluation),
            Err(ValidationFailure::Internal(_))
        ));
        let mut evaluation=graph.nodes.iter().find(|n|matches!(&n.payload,Some(Payload::Evaluation{bindings,..}) if !bindings.is_empty())).unwrap().clone();
        let Some(Payload::Evaluation { bindings, .. }) = &mut evaluation.payload else {
            unreachable!()
        };
        bindings[0].name = "other".into();
        assert!(matches!(
            environment.validate(&graph, &evaluation),
            Err(ValidationFailure::Internal(_))
        ));
    }
    fn guarded_example() -> ObservedEvaluation {
        let definitions = include_str!("../../tests/fixtures/counter.atoms.json").replace(
            "\"fields\": [",
            "\"fields\": [{\"name\":\"enabled\",\"type\":\"Bool\",\"meaning\":\"この状態への適用が有効。\"},",
        );
        let checked =
            crate::definition::check_definitions(&[("definition0", definitions.as_bytes())])
                .unwrap();
        let digest = &checked.vocabularies["Counter"].digest;
        let law = include_str!("../../tests/fixtures/counter.law")
            .replace("sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11", digest)
            .replace("law optional bounded(s: State):", "view other(s: State): Bool = true;\n  law optional bounded(s: State) when s.enabled:");
        let map = include_str!("../../tests/fixtures/counter.archmap.json")
            .replace("sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11", digest)
            .replace("\"value\": \"2\"", "\"value\": \"12\"")
            .replace("\"subjects\": [", "\"subjects\": [{\"id\":\"t\",\"type\":\"Counter.State\",\"origin\":\"model\"},")
            .replace("\"atoms\": [", "\"atoms\": [{\"id\":\"enabled-s\",\"subject\":\"s\",\"field\":\"Counter.State.enabled\",\"value\":true,\"origin\":\"model\"},{\"id\":\"enabled-t\",\"subject\":\"t\",\"field\":\"Counter.State.enabled\",\"value\":true,\"origin\":\"model\"},{\"id\":\"count-t\",\"subject\":\"t\",\"field\":\"Counter.State.count\",\"value\":\"12\",\"origin\":\"model\"},");
        evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![definitions.into_bytes()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &[
                "x=evaluate(CountAudit.other,s=@v/s)",
                "s=check(CountAudit.bounded,s=@v/s)",
                "t=check(CountAudit.bounded,s=@v/t)",
            ],
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn rejects_false_guard_value_and_unrelated_guard_occurrence() {
        let result = guarded_example();
        assert_eq!(result.status(), "complete");
        let mut control = Control::unlimited();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let mut graph = Graph::new(&control);
        graph.nodes = result.nodes.clone();
        let instance = graph
            .nodes
            .iter()
            .find(|n| matches!(n.payload, Some(Payload::LawInstance { .. })))
            .unwrap()
            .clone();
        let guard = instance.arguments[1];
        let Some(Payload::Evaluation {
            value: Some(value), ..
        }) = &graph.nodes[guard.0].payload
        else {
            unreachable!()
        };
        let value = *value;
        graph.nodes[value.0].payload = Some(Payload::Scalar(Scalar::Bool(false)));
        assert!(matches!(
            environment.validate(&graph, &instance),
            Err(ValidationFailure::Internal(_))
        ));
        graph.nodes = result.nodes.clone();
        let unrelated = result.answers[0].outputs["evaluation"];
        let Some(Payload::Evaluation {
            value: Some(literal_true),
            ..
        }) = &graph.nodes[unrelated.0].payload
        else {
            unreachable!()
        };
        let literal_true = *literal_true;
        let Some(Payload::Evaluation { value, parts, .. }) = &mut graph.nodes[guard.0].payload
        else {
            unreachable!()
        };
        *value = Some(literal_true);
        parts[0].value = Some(literal_true);
        // true の型・payload だけでは、元 enabled Atom の評価根拠を代用できない。
        assert!(matches!(
            environment.validate(&graph, &instance),
            Err(ValidationFailure::Internal(_))
        ));
        graph.nodes = result.nodes.clone();
        let mut wrong = instance.clone();
        wrong.arguments[1] = unrelated;
        assert!(matches!(
            environment.validate(&graph, &wrong),
            Err(ValidationFailure::Internal(_))
        ));
        // 同じ true でも Law に明記した guard とは異なる出現は使えない。
        let Some(Payload::Evaluation { expression, .. }) = &graph.nodes[unrelated.0].payload else {
            unreachable!()
        };
        let expression = *expression;
        let Some(Payload::LawInstance { guard, .. }) = &mut wrong.payload else {
            unreachable!()
        };
        *guard = Some(expression);
        assert!(matches!(
            environment.validate(&graph, &wrong),
            Err(ValidationFailure::Internal(_))
        ));
    }
    #[test]
    fn rejects_guard_binding_identity_and_missing_guard_support() {
        let result = guarded_example();
        let mut control = Control::unlimited();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let mut graph = Graph::new(&control);
        graph.nodes = result.nodes.clone();
        let instances: Vec<_> = graph
            .nodes
            .iter()
            .filter(|n| matches!(n.payload, Some(Payload::LawInstance { .. })))
            .cloned()
            .collect();
        let mut wrong = instances[0].clone();
        wrong.arguments[1] = instances[1].arguments[1];
        assert!(matches!(
            environment.validate(&graph, &wrong),
            Err(ValidationFailure::Internal(_))
        ));
        let mut wrong = instances[0].clone();
        wrong
            .support
            .retain(|f| f.field.as_deref() != Some("Counter.State.enabled"));
        assert!(matches!(
            environment.validate(&graph, &wrong),
            Err(ValidationFailure::Internal(_))
        ));
        let guard = instances[0].arguments[1];
        graph.nodes[guard.0]
            .support
            .retain(|f| f.field.as_deref() != Some("Counter.State.enabled"));
        assert!(matches!(
            environment.validate(&graph, &instances[0]),
            Err(ValidationFailure::Internal(_))
        ));
        graph.nodes = result.nodes.clone();
        let mut evaluation = graph.nodes[result.answers[1].outputs["evaluation"].0].clone();
        evaluation.arguments[2] = instances[1].arguments[1];
        assert!(matches!(
            environment.validate(&graph, &evaluation),
            Err(ValidationFailure::Internal(_))
        ));
    }

    fn rebuild_for_origin_and_support_recheck(
        result: &ObservedEvaluation,
        nodes: &[Node],
    ) -> Result<Graph, ValidationFailure> {
        let mut control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        let environment = Environment::new(result.prepared.inputs(), &mut control)
            .map_err(ValidationFailure::from)?;
        let mut graph = Graph::new(&control);
        graph.requests = result.prepared.requests().requests().to_vec();
        graph.frames = result.frames.clone();
        graph.iterations = result.iterations.clone();
        for (index, node) in nodes.iter().enumerate() {
            graph.active = result.contexts.get(index).copied().unwrap_or_default();
            environment.validate(&graph, node)?;
            graph.push(node.clone())?;
        }
        Ok(graph)
    }

    #[test]
    fn rejects_complete_answer_substitution_against_its_request() {
        let result = value_examples(false);
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("改変前の全nodeは元順の入力照合とGraph検査を通る");
        let mut control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let requests = result.prepared.requests().requests();
        for (request, answer) in requests.iter().zip(&result.answers) {
            environment
                .validate_answer(&graph, request, answer)
                .expect("元Requestとその正しいAnswerの組は総合検査を通る");
        }
        let amount = &result.answers[0];
        let zero = &result.answers[1];
        assert_eq!(amount.id, "amount");
        assert_eq!(zero.id, "zero");
        assert_eq!(amount.scope, zero.scope);
        assert_eq!(amount.status, zero.status);
        assert_eq!(
            graph.scalar(amount.outputs["value"]).unwrap(),
            &Scalar::Z(2.into())
        );
        assert_eq!(
            graph.scalar(zero.outputs["value"]).unwrap(),
            &Scalar::Z(0.into())
        );
        let mut wrong = amount.clone();
        wrong.outputs = zero.outputs.clone();
        // valueとEvaluationの双方は正しいzeroの組。id/status/scopeはamountのまま。
        assert_eq!(wrong.id, amount.id);
        assert_eq!(wrong.status, amount.status);
        assert_eq!(wrong.scope, amount.scope);
        assert!(
            matches!(
                environment.validate_answer(&graph, &requests[0], &wrong),
                Err(ValidationFailure::Internal(_))
            ),
            "正しい別宣言の出力ペアを元Requestの回答にできない"
        );
        let mut wrong_id = amount.clone();
        wrong_id.id = zero.id.clone();
        assert!(
            matches!(
                environment.validate_answer(&graph, &requests[0], &wrong_id),
                Err(ValidationFailure::Internal(_))
            ),
            "元式が同じでもAnswer.idは選択Requestへ帰属する"
        );

        let guarded = guarded_example();
        assert_eq!(guarded.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&guarded, &guarded.nodes)
            .expect("二つの明示束縛もともに有効な入力と導出である");
        let environment = Environment::new(guarded.prepared.inputs(), &mut control).unwrap();
        let requests = guarded.prepared.requests().requests();
        for (request, answer) in requests.iter().zip(&guarded.answers) {
            environment
                .validate_answer(&graph, request, answer)
                .unwrap();
        }
        let first = &guarded.answers[1];
        let second = &guarded.answers[2];
        assert_eq!(first.id, "s");
        assert_eq!(second.id, "t");
        assert_eq!(first.status, Decision::Refuted);
        assert_eq!(first.status, second.status);
        assert_eq!(first.scope, second.scope);
        assert_eq!(requests[1].declaration(), requests[2].declaration());
        assert_ne!(requests[1].arguments, requests[2].arguments);
        let mut wrong_binding = first.clone();
        wrong_binding.outputs = second.outputs.clone();
        wrong_binding.claim = second.claim;
        wrong_binding.evidence = second.evidence.clone();
        wrong_binding.reasons = second.reasons.clone();
        assert!(
            matches!(
                environment.validate_answer(&graph, &requests[1], &wrong_binding),
                Err(ValidationFailure::Internal(_))
            ),
            "同じ宣言/値/判断でも別subjectへの明示束縛の回答を流用できない"
        );
    }

    #[test]
    fn rejects_self_consistent_removal_of_body_support_and_counterexample_facts() {
        let result = example();
        assert_eq!(result.status(), "complete");
        let original = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("改変前Counter12の全導出は元順で再検査できる");
        let answer = &result.answers[0];
        assert_eq!(answer.status, Decision::Refuted);
        let body = answer.outputs["evaluation"];
        let claim = answer.claim.unwrap();
        let Some(Payload::Proposition { instance }) = &result.nodes[claim.0].payload else {
            panic!("元のclaimはLawInstanceを指す命題");
        };
        let instance = *instance;
        let Some(Payload::LawInstance { guard, .. }) = &result.nodes[instance.0].payload else {
            unreachable!()
        };
        assert!(
            guard.is_none(),
            "明示guardを介さないbody支持の経路を検査する"
        );
        let Some(Payload::Evaluation {
            value: Some(value),
            parts,
            ..
        }) = &result.nodes[body.0].payload
        else {
            panic!("比較bodyは値と元の子評価を保持する");
        };
        assert_eq!(original.scalar(*value).unwrap(), &Scalar::Bool(false));
        assert!(!parts[0].children.is_empty());
        let count_fact = result.nodes[body.0]
            .support
            .iter()
            .find(|f| {
                f.field.as_deref() == Some("Counter.State.count")
                    && f.atom.as_deref() == Some("count")
            })
            .expect("元bodyはcount=12の実在Atomを使用する")
            .clone();
        let mut changed = result.nodes.clone();
        let mut affected = vec![body.0, instance.0, claim.0];
        affected.extend(answer.evidence.iter().map(|r| r.0));
        affected.sort_unstable();
        affected.dedup();
        let (mut evaluation_evidence, mut counterexample) = (false, false);
        for index in affected {
            assert!(changed[index].support.contains(&count_fact));
            changed[index].support.clear();
            match &mut changed[index].payload {
                Some(Payload::EvaluationEvidence { .. }) => evaluation_evidence = true,
                Some(Payload::Counterexample {
                    left, right, facts, ..
                }) => {
                    counterexample = true;
                    assert_eq!(original.scalar(*left).unwrap(), &Scalar::Z(12.into()));
                    assert_eq!(original.scalar(*right).unwrap(), &Scalar::Z(10.into()));
                    assert!(facts.contains(&count_fact));
                    facts.clear();
                }
                _ => {}
            }
        }
        assert!(evaluation_evidence && counterexample);
        // 子値・子Evaluationには元支持を残す。bodyと全下流を空へ揃えただけである。
        assert!(
            parts[0]
                .children
                .iter()
                .any(|r| changed[r.0].support.contains(&count_fact))
        );
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "body/instance/証拠/命題の自己一致だけで元count支持を削除できない"
        );

        // Law適用経路に限らず、値を返すamountも元field読取りの支持を省略できない。
        let values = value_examples(false);
        assert_eq!(values.status(), "complete");
        rebuild_for_origin_and_support_recheck(&values, &values.nodes)
            .expect("改変前のamountも全nodeを元順で再検査できる");
        let mut changed = values.nodes.clone();
        let amount = values.answers[0].outputs["evaluation"];
        assert!(
            changed[amount.0]
                .support
                .iter()
                .any(|f| f.field.as_deref() == Some("Counter.State.count"))
        );
        changed[amount.0].support.clear();
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&values, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "evaluateの通常値でも元fieldの使用事実を失えない"
        );
    }
    fn assert_only_scalar_origin_mode_substitution_is_rejected(
        result: &ObservedEvaluation,
        reference: NodeRef,
        label: &str,
    ) {
        let original = &result.nodes[reference.0];
        assert!(
            matches!(original.payload, Some(Payload::Scalar(_))),
            "{label}"
        );
        assert_eq!(
            original.scope.modes,
            std::collections::BTreeSet::from(["specification".to_owned()]),
            "{label}"
        );
        let mut changed = result.nodes.clone();
        changed[reference.0].scope.modes =
            std::collections::BTreeSet::from(["observed".to_owned()]);
        assert_eq!(changed[reference.0].support, original.support);
        assert_eq!(changed[reference.0].arguments, original.arguments);
        assert_eq!(changed[reference.0].scope.readings, original.scope.readings);
        assert_eq!(
            changed[reference.0].scope.snapshots,
            original.scope.snapshots
        );
        // 値・支持・Ref・Answerを元のまま保ち、Scalar単独のmodeだけを偽装する。
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "{label}: 元入力がspecificationであるScalarをobservedへ付け替えられない"
        );
    }

    #[test]
    fn rejects_scalar_origin_scope_substitution_under_an_unchanged_answer() {
        let result = value_examples(false);
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("改変前の全Scalarと導出は元入力のScopeで再検査できる");
        let answer = |id: &str| result.answers.iter().find(|a| a.id == id).unwrap();
        let amount = answer("amount");
        let amount_evaluation = amount.outputs["evaluation"];
        let Some(Payload::Evaluation { bindings, .. }) = &result.nodes[amount_evaluation.0].payload
        else {
            panic!("amountの実束縛を保持するEvaluation");
        };
        assert_eq!(bindings[0].name, "s");
        let subject = bindings[0].value;
        assert!(
            matches!(graph.scalar(subject).unwrap(), Scalar::Subject { snapshot, subject, .. } if snapshot == "v" && subject == "s")
        );
        let mut targets = vec![("明示bindingのsubject", subject)];
        for (id, expected) in [
            ("amount", Scalar::Z(2.into())),
            ("zero", Scalar::Z(0.into())),
            ("yes", Scalar::Bool(true)),
            ("no", Scalar::Bool(false)),
            ("negative", Scalar::Z((-2).into())),
            ("same", Scalar::Bool(false)),
            ("sameBool", Scalar::Bool(false)),
        ] {
            let value = answer(id).outputs["value"];
            assert_eq!(
                graph.scalar(value).unwrap(),
                &expected,
                "{id}の正常baseline値"
            );
            targets.push((id, value));
        }
        let Some(Payload::Evaluation { parts, .. }) =
            &result.nodes[answer("same").outputs["evaluation"].0].payload
        else {
            panic!("Z等号のEvaluation");
        };
        let residual = parts[0].residual.expect("Z等号の元左右の差を保持する");
        assert_eq!(graph.scalar(residual).unwrap(), &Scalar::Z((-8).into()));
        targets.push(("Z等号の残差", residual));
        for (label, reference) in targets {
            assert_only_scalar_origin_mode_substitution_is_rejected(&result, reference, label);
        }

        // Bool Lawで生成する固定trueも、元の適用Scopeに帰属するScalarである。
        let law = include_str!("../../tests/fixtures/counter.law").replace(
            "view amount(s: State): Z = s.count;",
            "law required truth(s: State): true;\n  view amount(s: State): Z = s.count;",
        );
        let mut control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        let truth = evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![include_bytes!("../../tests/fixtures/counter.atoms.json").to_vec()],
                law.into_bytes(),
                include_bytes!("../../tests/fixtures/counter.archmap.json").to_vec(),
            ),
            &["truth=check(CountCheck.truth,s=@v/s)"],
            &mut control,
        )
        .unwrap();
        assert_eq!(truth.status(), "complete");
        assert_eq!(truth.answers[0].status, Decision::Established);
        let graph = rebuild_for_origin_and_support_recheck(&truth, &truth.nodes)
            .expect("固定trueを含むBool Lawの正常Scope/支持で再buildできる");
        let fixed = truth
            .nodes
            .iter()
            .enumerate()
            .find(|(_, n)| {
                matches!(&n.rule, Rule::Construction("proposition"))
                    && matches!(&n.payload, Some(Payload::Scalar(Scalar::Bool(true))))
            })
            .map(|(i, _)| NodeRef(i))
            .expect("Bool Lawの証拠が使う固定true Scalar");
        assert_eq!(graph.scalar(fixed).unwrap(), &Scalar::Bool(true));
        assert!(
            truth.nodes[fixed.0].support.is_empty(),
            "固定規則に架空のAtom支持はない"
        );
        assert_only_scalar_origin_mode_substitution_is_rejected(
            &truth,
            fixed,
            "固定proposition true",
        );
    }

    #[test]
    fn accepts_two_hop_reference_with_distinct_scalar_leaf_and_expression_scopes() {
        let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
      "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Counter","version":"1",
      "dependencies":[],"declarations":[{"kind":"entity","name":"Counter.State","meaning":"次の状態への参照を持つ。",
      "parameters":[],"fields":[{"name":"count","type":"Z","meaning":"保持する件数。"},
      {"name":"next","type":["Ref","Counter.State"],"meaning":"次に参照する状態。"}],"alignments":[]}]}]}"#;
        let checked =
            crate::definition::check_definitions(&[("definition0", definitions.as_bytes())])
                .unwrap();
        let digest = &checked.vocabularies["Counter"].digest;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Follow {{
  use vocabulary Counter version "1" digest "{digest}";
  view amount(s: State): Z = ((s.next).next).count;
}}
"#
        );
        let map = format!(
            r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Counter","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"source","uri":"urn:fixture:two-hop","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[
        {{"id":"seen","mode":"observed","method":"参照を観測する。","locations":[{{"source":"source","path":"state.model","span":[0,4]}}]}},
        {{"id":"plan","mode":"proposed","method":"次の参照を提示する。","locations":[],"note":"提案する状態tの参照先をuとする。"}},
        {{"id":"model","mode":"specification","method":"末尾状態を提示する。","locations":[],"note":"仕様状態uの件数は7。"}}],
      "snapshots":[
        {{"id":"v","origin":"seen","subjects":[{{"id":"s","type":"Counter.State","origin":"seen"}}],
          "atoms":[{{"id":"next-s","subject":"s","field":"Counter.State.next","value":["w","t"],"origin":"seen"}}]}},
        {{"id":"w","origin":"plan","subjects":[{{"id":"t","type":"Counter.State","origin":"plan"}}],
          "atoms":[{{"id":"next-t","subject":"t","field":"Counter.State.next","value":["x","u"],"origin":"plan"}}]}},
        {{"id":"x","origin":"model","subjects":[{{"id":"u","type":"Counter.State","origin":"model"}}],
          "atoms":[{{"id":"count-u","subject":"u","field":"Counter.State.count","value":"7","origin":"model"}}]}}]}}"#
        );
        let mut control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        let result = evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![definitions.as_bytes().to_vec()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &["n=evaluate(Follow.amount,s=@v/s)"],
            &mut control,
        )
        .expect("各snapshot内のmodeを一致させた三入力は有効");
        assert_eq!(result.status(), "complete");
        let answer = &result.answers[0];
        assert_eq!(answer.status, Decision::Established);
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("異なる実由来を持つ二hopの全nodeを元順で再検査できる");
        let value = answer.outputs["value"];
        assert_eq!(graph.scalar(value).unwrap(), &Scalar::Z(7.into()));
        let leaf = &graph.nodes[value.0];
        assert!(matches!(&leaf.rule, Rule::Input { kind: "atom", .. }));
        let set = |values: &[&str]| {
            values
                .iter()
                .map(|s| (*s).to_owned())
                .collect::<std::collections::BTreeSet<_>>()
        };
        assert_eq!(leaf.scope.readings, set(&["Follow"]));
        // Scalarは明示束縛sと実際に読んだu.countの原始leafに帰属する。
        assert_eq!(leaf.scope.snapshots, set(&["v", "x"]));
        assert_eq!(leaf.scope.modes, set(&["observed", "specification"]));
        assert!(!leaf.scope.completions);
        assert!(leaf.support.iter().any(|f| f.snapshot == "x"
            && f.subject == "u"
            && f.field.as_deref() == Some("Counter.State.count")
            && f.atom.as_deref() == Some("count-u")));
        let evaluation = &graph.nodes[answer.outputs["evaluation"].0];
        let Some(Payload::Evaluation {
            value: evaluated, ..
        }) = &evaluation.payload
        else {
            panic!("元の二hop式を持つEvaluation");
        };
        assert_eq!(*evaluated, Some(value));
        // 式全体は経由したw/tの提案originも根拠に含む。
        assert_eq!(evaluation.scope.snapshots, set(&["v", "w", "x"]));
        assert_eq!(
            evaluation.scope.modes,
            set(&["observed", "proposed", "specification"])
        );
        assert_eq!(answer.scope, evaluation.scope);
        assert_ne!(leaf.scope, evaluation.scope);
        for (snapshot, subject, atom, field) in [
            ("v", "s", "next-s", "Counter.State.next"),
            ("w", "t", "next-t", "Counter.State.next"),
            ("x", "u", "count-u", "Counter.State.count"),
        ] {
            assert!(evaluation.support.iter().any(|f| f.snapshot == snapshot
                && f.subject == subject
                && f.atom.as_deref() == Some(atom)
                && f.field.as_deref() == Some(field)));
        }
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        environment
            .validate_answer(&graph, &result.prepared.requests().requests()[0], answer)
            .expect("Scalar leafと式全体のScopeが異なる正常Answerも総合検査を通る");
    }
    fn ac2_private_guard_example(gate: Option<bool>, body: Option<bool>) -> ObservedEvaluation {
        let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
      "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Signal","version":"1",
      "dependencies":[],"declarations":[{"kind":"entity","name":"Signal.Cell","meaning":"二つのBool値を保持する対象。",
      "parameters":[],"fields":[{"name":"gate","type":"Bool","meaning":"適用条件。"},
      {"name":"payload","type":"Bool","meaning":"検査する値。"}],"alignments":[]}]}]}"#;
        let checked =
            crate::definition::check_definitions(&[("definition0", definitions.as_bytes())])
                .unwrap();
        let digest = &checked.vocabularies["Signal"].digest;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading R {{
  use vocabulary Signal version "1" digest "{digest}";
  view yes(item: Cell): Bool = true;
  view no(item: Cell): Bool = false;
  view zero(item: Cell): Z = 0;
  law required condition(item: Cell) when item.gate: item.payload;
}}
"#
        );
        let mut atoms = vec![];
        for subject in ["s", "t"] {
            for (field, value) in [("gate", gate), ("payload", body)] {
                if let Some(value) = value {
                    atoms.push(format!(r#"{{"id":"{subject}-{field}","subject":"{subject}","field":"Signal.Cell.{field}","value":{value},"origin":"model"}}"#));
                }
            }
        }
        let atoms = atoms.join(",");
        let map = format!(
            r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Signal","version":"1","digest":"{digest}"}}],"sources":[],
      "origins":[{{"id":"model","mode":"specification","method":"二つの対象を提示する。","locations":[],"note":"Bool条件と値の小さい仕様モデル。"}}],
      "snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"s","type":"Signal.Cell","origin":"model"}},{{"id":"t","type":"Signal.Cell","origin":"model"}}],"atoms":[{atoms}]}}]}}"#
        );
        let mut control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![definitions.as_bytes().to_vec()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &[
                "yes=evaluate(R.yes,item=@v/s)",
                "no=evaluate(R.no,item=@v/s)",
                "zero=evaluate(R.zero,item=@v/s)",
                "s=check(R.condition,item=@v/s)",
                "t=check(R.condition,item=@v/t)",
            ],
            &mut control,
        )
        .unwrap()
    }

    #[test]
    fn rejects_false_guard_applicability_conditional_value_and_bool_residual_forgery() {
        let result = ac2_private_guard_example(Some(false), Some(false));
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("false guardの正規DAGを元順で再buildできる");
        let answer = result.answers.iter().find(|a| a.id == "s").unwrap();
        assert_eq!(answer.status, Decision::Established);
        let root = answer.outputs["evaluation"];
        let Some(Payload::Evaluation {
            value: Some(value),
            applicability,
            ..
        }) = &result.nodes[root.0].payload
        else {
            panic!("条件付き評価")
        };
        assert_eq!(*applicability, "not_applicable");
        assert_eq!(graph.scalar(*value).unwrap(), &Scalar::Bool(true));
        let mut changed = result.nodes.clone();
        changed[value.0].payload = Some(Payload::Scalar(Scalar::Bool(false)));
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "同じ構成入力でも含意Scalarの値を偽装できない"
        );
        for claimed in ["applicable", "undetermined"] {
            let mut changed = result.nodes.clone();
            let Some(Payload::Evaluation { applicability, .. }) = &mut changed[root.0].payload
            else {
                unreachable!()
            };
            *applicability = claimed;
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "false guardの実評価に反するapplicabilityを拒否する"
            );
        }
        let false_value = result
            .answers
            .iter()
            .find(|a| a.id == "no")
            .unwrap()
            .outputs["value"];
        let mut changed = result.nodes.clone();
        let Some(Payload::Evaluation { value, .. }) = &mut changed[root.0].payload else {
            unreachable!()
        };
        *value = Some(false_value);
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "非適用Lawをraw falseの反証へ変換できない"
        );
        let zero = result
            .answers
            .iter()
            .find(|a| a.id == "zero")
            .unwrap()
            .outputs["value"];
        let mut changed = result.nodes.clone();
        let Some(Payload::Evaluation { parts, .. }) = &mut changed[root.0].payload else {
            unreachable!()
        };
        assert!(parts.iter().all(|p| p.residual.is_none()));
        parts[0].residual = Some(zero);
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "一般BoolへZ残差を捏造できない"
        );
    }

    #[test]
    fn rejects_conditional_guard_and_body_from_different_explicit_bindings() {
        let result = ac2_private_guard_example(Some(false), Some(false));
        assert_eq!(result.status(), "complete");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("二つの正規明示束縛のDAG");
        let first = result.answers.iter().find(|a| a.id == "s").unwrap().outputs["evaluation"];
        let second = result.answers.iter().find(|a| a.id == "t").unwrap().outputs["evaluation"];
        let Some(Payload::Evaluation {
            parts: other_parts, ..
        }) = &result.nodes[first.0].payload
        else {
            panic!("guard/bodyの各原式評価")
        };
        for part in [0, 1] {
            let mut changed = result.nodes.clone();
            let Some(Payload::Evaluation { parts, .. }) = &mut changed[second.0].payload else {
                unreachable!()
            };
            assert_eq!(parts[part].location, other_parts[part].location);
            assert!(!other_parts[part].children.is_empty());
            assert!(
                other_parts[part]
                    .children
                    .iter()
                    .all(|child| child.0 < second.0)
            );
            parts[part].children = other_parts[part].children.clone();
            // 元式span・値が同じでも別subjectのguard/bodyを同じLaw適用へ混ぜない。
            assert!(matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ));
        }
    }

    #[test]
    fn rejects_determinate_values_or_judgments_for_missing_guard_and_false_body() {
        let result = ac2_private_guard_example(None, Some(false));
        assert_eq!(result.status(), "partial");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("未観測guardとfalse bodyの正規DAGを再buildできる");
        let answer_index = result.answers.iter().position(|a| a.id == "s").unwrap();
        let answer = &result.answers[answer_index];
        assert_eq!(answer.status, Decision::Undetermined);
        let root = answer.outputs["evaluation"];
        let Some(Payload::Evaluation {
            value,
            applicability,
            ..
        }) = &result.nodes[root.0].payload
        else {
            panic!("条件付き評価")
        };
        assert!(value.is_none());
        assert_eq!(*applicability, "undetermined");
        for id in ["yes", "no"] {
            let replacement = result.answers.iter().find(|a| a.id == id).unwrap().outputs["value"];
            let mut changed = result.nodes.clone();
            let Some(Payload::Evaluation { value, .. }) = &mut changed[root.0].payload else {
                unreachable!()
            };
            *value = Some(replacement);
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "補完で真偽が異なるLawへ確定値を補えない"
            );
        }
        let mut control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        environment
            .validate_answer(
                &graph,
                &result.prepared.requests().requests()[answer_index],
                answer,
            )
            .unwrap();
        for status in [Decision::Established, Decision::Refuted] {
            let mut wrong = answer.clone();
            wrong.status = status;
            assert!(matches!(
                environment.validate_answer(
                    &graph,
                    &result.prepared.requests().requests()[answer_index],
                    &wrong
                ),
                Err(ValidationFailure::Internal(_))
            ));
        }
    }
    fn scalar_operation_private_example(p: Option<bool>, q: Option<bool>) -> ObservedEvaluation {
        let definitions=include_str!("../../tests/fixtures/counter.atoms.json").replace("\"fields\": [",
        "\"fields\": [{\"name\":\"other\",\"type\":\"Z\",\"meaning\":\"第二整数。\"},{\"name\":\"p\",\"type\":\"Bool\",\"meaning\":\"第一条件。\"},{\"name\":\"q\",\"type\":\"Bool\",\"meaning\":\"第二条件。\"},");
        let checked =
            crate::definition::check_definitions(&[("definition0", definitions.as_bytes())])
                .unwrap();
        let digest = &checked.vocabularies["Counter"].digest;
        let law = include_str!("../../tests/fixtures/counter.law")
            .replace(
                "sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11",
                digest,
            )
            .replace(
                "view amount(s: State): Z = s.count;",
                r#"view amount(s: State): Z = s.count;
          view total(s: State): Z = s.count + s.other;
          view difference(s: State): Z = s.count - s.other;
          view product(s: State): Z = s.count * s.other;
          view foreign_add(s: State): Z = s.count + 1;
          view foreign_subtract(s: State): Z = s.count - 1;
          view foreign_product(s: State): Z = s.count * 1;
          view add_zero(s: State): Z = s.count + 0;
          view disjunction(s: State): Bool = s.p or s.q;
          view conjunction(s: State): Bool = s.p and s.q;
          view consequence(s: State): Bool = s.p implies s.q;
          view yes(s: State): Bool = true;
          view no(s: State): Bool = false;
          law required computed(s: State): s.count + s.other = 10;"#,
            );
        let mut additions=vec![r#"{"id":"other","subject":"s","field":"Counter.State.other","value":"3","origin":"model"}"#.to_owned()];
        for (field, value) in [("p", p), ("q", q)] {
            if let Some(value) = value {
                additions.push(format!(r#"{{"id":"{field}","subject":"s","field":"Counter.State.{field}","value":{value},"origin":"model"}}"#));
            }
        }
        let additions = additions.join(",");
        let map = include_str!("../../tests/fixtures/counter.archmap.json")
            .replace(
                "sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11",
                digest,
            )
            .replace("\"value\": \"2\"", "\"value\": \"7\"")
            .replace(
                "件数が2である仕様モデル。",
                "件数と条件を提示する仕様モデル。",
            )
            .replace("\"atoms\": [", &format!("\"atoms\": [{additions},"));
        let mut control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![definitions.into_bytes()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &[
                "yes=evaluate(CountCheck.yes,s=@v/s)",
                "no=evaluate(CountCheck.no,s=@v/s)",
                "total=evaluate(CountCheck.total,s=@v/s)",
                "difference=evaluate(CountCheck.difference,s=@v/s)",
                "product=evaluate(CountCheck.product,s=@v/s)",
                "add_zero=evaluate(CountCheck.add_zero,s=@v/s)",
                "or_value=evaluate(CountCheck.disjunction,s=@v/s)",
                "and_value=evaluate(CountCheck.conjunction,s=@v/s)",
                "imp_value=evaluate(CountCheck.consequence,s=@v/s)",
                "computed=check(CountCheck.computed,s=@v/s)",
            ],
            &mut control,
        )
        .unwrap()
    }

    #[test]
    fn rejects_arithmetic_value_and_commutative_argument_substitution() {
        let result = scalar_operation_private_example(Some(false), Some(true));
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("正常な整数演算DAGを元順で再buildする");
        for (id, expected) in [("total", 10), ("difference", 4), ("product", 21)] {
            let reference = result.answers.iter().find(|a| a.id == id).unwrap().outputs["value"];
            assert_eq!(
                graph.scalar(reference).unwrap(),
                &Scalar::Z(expected.into())
            );
            let mut changed = result.nodes.clone();
            changed[reference.0].payload = Some(Payload::Scalar(Scalar::Z(99.into())));
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "元ASTと入力に反する整数値を拒否する"
            );
        }
        let sum = result
            .answers
            .iter()
            .find(|a| a.id == "total")
            .unwrap()
            .outputs["value"];
        let mut changed = result.nodes.clone();
        assert_eq!(changed[sum.0].arguments.len(), 2);
        assert_ne!(
            graph.scalar(changed[sum.0].arguments[0]).unwrap(),
            graph.scalar(changed[sum.0].arguments[1]).unwrap()
        );
        changed[sum.0].arguments.swap(0, 1);
        // 7+3=3+7で値10は同じでも、元の左右fieldの出現と既出Ref identityは異なる。
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "可換な値だけの一致で元ASTの左右を置換できない"
        );
    }

    #[test]
    fn rejects_short_circuit_value_and_foreign_operand_evaluation_substitution() {
        let result = scalar_operation_private_example(None, Some(false));
        assert_eq!(result.status(), "partial");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("未知pとfalse qの全raw評価を保つ正常DAG");
        let answer = result.answers.iter().find(|a| a.id == "and_value").unwrap();
        assert_eq!(answer.status, Decision::Established);
        let value = answer.outputs["value"];
        assert_eq!(graph.scalar(value).unwrap(), &Scalar::Bool(false));
        let mut changed = result.nodes.clone();
        changed[value.0].payload = Some(Payload::Scalar(Scalar::Bool(true)));
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "x and falseは全補完でfalseでありtrueへ変更できない"
        );
        let prior_or = result
            .answers
            .iter()
            .find(|a| a.id == "or_value")
            .unwrap()
            .outputs["evaluation"];
        let Some(Payload::Evaluation { parts, .. }) = &result.nodes[prior_or.0].payload else {
            panic!("先行orの元子Evaluation")
        };
        let foreign = parts[0].children[0];
        assert!(foreign.0 < value.0, "代替は既出の同型p Evaluation");
        let mut changed = result.nodes.clone();
        assert_eq!(changed[value.0].arguments.len(), 2);
        assert_ne!(changed[value.0].arguments[0], foreign);
        assert_eq!(
            result.nodes[changed[value.0].arguments[0].0].ty,
            result.nodes[foreign.0].ty
        );
        changed[value.0].arguments[0] = foreign;
        // 同じsubjectの同じ未知slotを読む子でも、別の元AST出現を混ぜない。
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(&result, &changed),
            Err(ValidationFailure::Internal(_))
        ));
    }

    #[test]
    fn rejects_scalar_operation_support_and_scope_pair_substitution() {
        let result = scalar_operation_private_example(Some(false), Some(true));
        assert_eq!(result.status(), "complete");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("支持とScopeの正常baseline");
        for id in ["total", "and_value"] {
            let answer = result.answers.iter().find(|a| a.id == id).unwrap();
            let value = answer.outputs["value"];
            let evaluation = answer.outputs["evaluation"];
            let Some(Payload::Evaluation { expression, .. }) = &result.nodes[evaluation.0].payload
            else {
                panic!("元演算のEvaluation")
            };
            let expression = *expression;
            assert!(!result.nodes[value.0].support.is_empty());
            let mut changed = result.nodes.clone();
            changed[value.0].support.clear();
            changed[evaluation.0].support.clear();
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "値とEvaluationの支持を空へ揃えても原始field由来を削除できない"
            );
            let mut changed = result.nodes.clone();
            for reference in [expression, value, evaluation] {
                changed[reference.0].scope.modes =
                    std::collections::BTreeSet::from(["observed".to_owned()]);
            }
            let mut forged_answer = answer.clone();
            forged_answer.scope.modes = std::collections::BTreeSet::from(["observed".to_owned()]);
            assert_eq!(forged_answer.scope, changed[evaluation.0].scope);
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "Source/Scalar/Evaluation/Answerのmode自己一致でも元仕様originをobservedへ変更できない"
            );
        }
    }
    #[test]
    fn rejects_arithmetic_scalar_rule_span_from_a_different_same_operator_occurrence() {
        let result = scalar_operation_private_example(Some(false), Some(true));
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("外来の未選択宣言を含む正常fixtureの全nodeは元順で再検査できる");
        for (id, foreign_name, expected_op, value, foreign_value) in [
            ("total", "CountCheck.foreign_add", BinOp::Add, 10, 8),
            (
                "difference",
                "CountCheck.foreign_subtract",
                BinOp::Sub,
                4,
                6,
            ),
            ("product", "CountCheck.foreign_product", BinOp::Mul, 21, 7),
        ] {
            assert!(
                result
                    .prepared
                    .requests()
                    .requests()
                    .iter()
                    .all(|r| r.declaration() != foreign_name)
            );
            let foreign = &result.prepared.inputs().law().declarations[foreign_name];
            let Signature::View { body, returns, .. } = &foreign.signature else {
                panic!("型付きの外来view")
            };
            assert_eq!(returns, &Type::Z);
            let foreign_ast = &result.prepared.inputs().law().exprs[*body];
            let ExprKind::Binary { op, rhs, .. } = &foreign_ast.kind else {
                panic!("元と同型・同演算子の二項AST")
            };
            assert_eq!(*op, expected_op);
            assert!(
                matches!(&result.prepared.inputs().law().exprs[*rhs].kind, ExprKind::Int(n) if n=="1")
            );
            assert_ne!(
                value, foreign_value,
                "実count=7に対する外来式の手計算値は元の値と異なる"
            );
            let answer = result.answers.iter().find(|a| a.id == id).unwrap();
            let reference = answer.outputs["value"];
            assert_eq!(graph.scalar(reference).unwrap(), &Scalar::Z(value.into()));
            let original = &result.nodes[reference.0];
            let Rule::Input {
                kind: "law",
                location: Location::Law {
                    span: original_span,
                },
            } = &original.rule
            else {
                panic!("元の算術値は元Law出現を根とする")
            };
            assert_ne!(*original_span, foreign_ast.span);
            assert_eq!(original.arguments.len(), 2);
            assert_eq!(
                graph.scalar(original.arguments[0]).unwrap(),
                &Scalar::Z(7.into())
            );
            assert_eq!(
                graph.scalar(original.arguments[1]).unwrap(),
                &Scalar::Z(3.into())
            );
            let mut changed = result.nodes.clone();
            // 唯一の変更はRule.location.span。値/args/支持/Scope/親Eval/Answerは変更しない。
            changed[reference.0].rule = Rule::Input {
                kind: "law",
                location: Location::Law {
                    span: foreign_ast.span,
                },
            };
            assert_eq!(changed[reference.0].arguments, original.arguments);
            assert_eq!(changed[reference.0].support, original.support);
            assert_eq!(changed[reference.0].scope, original.scope);
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "同じ演算子だけの一致で別AST出現へScalarの帰属を変更できない"
            );
        }
    }

    #[test]
    fn rejects_addition_scalar_relabelled_as_an_integer_residual_rule() {
        let result = scalar_operation_private_example(Some(false), Some(true));
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("count+0を含む正規DAGと由来を元順で再検査できる");
        let answer = result.answers.iter().find(|a| a.id == "add_zero").unwrap();
        let reference = answer.outputs["value"];
        let original = &result.nodes[reference.0];
        assert_eq!(graph.scalar(reference).unwrap(), &Scalar::Z(7.into()));
        assert_eq!(original.arguments.len(), 2);
        assert_eq!(
            graph.scalar(original.arguments[0]).unwrap(),
            &Scalar::Z(7.into())
        );
        assert_eq!(
            graph.scalar(original.arguments[1]).unwrap(),
            &Scalar::Z(0.into())
        );
        let Rule::Input {
            kind: "law",
            location: Location::Law { span },
        } = &original.rule
        else {
            panic!("元の加算Rule")
        };
        let expression = result
            .prepared
            .inputs()
            .law()
            .exprs
            .iter()
            .find(|e| e.span == *span)
            .unwrap();
        assert!(matches!(
            &expression.kind,
            ExprKind::Binary { op: BinOp::Add, .. }
        ));
        let mut changed = result.nodes.clone();
        // 7+0と7-0は値も二つのargsも一致する。元の加算を残差構成へ読み替えない。
        changed[reference.0].rule = Rule::Construction("evaluation");
        assert_eq!(changed[reference.0].arguments, original.arguments);
        assert_eq!(changed[reference.0].support, original.support);
        assert_eq!(changed[reference.0].scope, original.scope);
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "値と引数が同じでも算術Scalarの元source kindを残差へ付け替えられない"
        );
    }
    #[test]
    fn rejects_integer_equality_residual_relabelled_as_a_foreign_subtraction() {
        let result = scalar_operation_private_example(Some(false), Some(true));
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("元の算術値と等式残差を持つ正規DAG");
        let answer = result.answers.iter().find(|a| a.id == "computed").unwrap();
        let evaluation = answer.outputs["evaluation"];
        let Some(Payload::Evaluation { parts, .. }) = &result.nodes[evaluation.0].payload else {
            panic!("数値等式の元評価")
        };
        let residual = parts[0].residual.expect("数値等式の残差");
        assert_eq!(graph.scalar(residual).unwrap(), &Scalar::Z(0.into()));
        assert!(matches!(
            &result.nodes[residual.0].rule,
            Rule::Construction("evaluation")
        ));
        assert_eq!(result.nodes[residual.0].arguments.len(), 2);
        for argument in &result.nodes[residual.0].arguments {
            assert_eq!(graph.scalar(*argument).unwrap(), &Scalar::Z(10.into()));
        }
        let foreign = &result.prepared.inputs().law().declarations["CountCheck.foreign_subtract"];
        let Signature::View { body, .. } = &foreign.signature else {
            panic!("未選択view")
        };
        let foreign = &result.prepared.inputs().law().exprs[*body];
        assert!(matches!(
            &foreign.kind,
            ExprKind::Binary { op: BinOp::Sub, .. }
        ));
        let mut changed = result.nodes.clone();
        changed[residual.0].rule = Rule::Input {
            kind: "law",
            location: Location::Law { span: foreign.span },
        };
        // 値0と引数10/10、支持・Scope・親評価は保ち、残差の生成規則だけを変える。
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "数値等式残差を別ASTの減算出所へ読み替えられない"
        );
    }
    // evaluate.rs の既存 #[cfg(test)] mod recheck_tests 内へ追加する。
    // 既存 scalar_operation_private_example / rebuild_for_origin_and_support_recheck を使う。
    #[test]
    fn rejects_foreign_arithmetic_rule_span_in_a_scalar_only_dag_prefix() {
        let result = scalar_operation_private_example(Some(false), Some(true));
        assert_eq!(result.status(), "complete");
        for (id, foreign_name, expected_op, expected) in [
            ("total", "CountCheck.foreign_add", BinOp::Add, 10),
            ("difference", "CountCheck.foreign_subtract", BinOp::Sub, 4),
            ("product", "CountCheck.foreign_product", BinOp::Mul, 21),
        ] {
            let answer = result.answers.iter().find(|a| a.id == id).unwrap();
            let reference = answer.outputs["value"];
            let parent_evaluation = answer.outputs["evaluation"];
            assert!(
                reference.0 < parent_evaluation.0,
                "Scalar push後・親Evaluation未挿入のprefix"
            );
            let prefix = &result.nodes[..=reference.0];
            let graph = rebuild_for_origin_and_support_recheck(&result, prefix)
                .expect("親Evaluationを待たずとも保持可能な正常prefixは元順再検査を通る");
            assert_eq!(
                graph.scalar(reference).unwrap(),
                &Scalar::Z(expected.into())
            );
            assert!(
                graph.get(parent_evaluation).is_err(),
                "親Evaluationによる後続検査はこのprefixにない"
            );
            assert!(
                result
                    .prepared
                    .requests()
                    .requests()
                    .iter()
                    .all(|r| r.declaration() != foreign_name)
            );
            let foreign = &result.prepared.inputs().law().declarations[foreign_name];
            let Signature::View { body, returns, .. } = &foreign.signature else {
                panic!("検査済みの未選択Z view")
            };
            assert_eq!(returns, &Type::Z);
            let foreign_ast = &result.prepared.inputs().law().exprs[*body];
            let ExprKind::Binary { op, rhs, .. } = &foreign_ast.kind else {
                panic!("同型・同演算子の別出現")
            };
            assert_eq!(*op, expected_op);
            assert!(
                matches!(&result.prepared.inputs().law().exprs[*rhs].kind, ExprKind::Int(n) if n == "1")
            );
            let original = &prefix[reference.0];
            let Rule::Input {
                kind: "law",
                location: Location::Law { span },
            } = &original.rule
            else {
                panic!("元算術ScalarのLaw Rule")
            };
            assert_ne!(*span, foreign_ast.span);
            assert_eq!(original.arguments.len(), 2);
            assert!(original.arguments.iter().all(|r| r.0 < reference.0));
            assert_eq!(
                graph.scalar(original.arguments[0]).unwrap(),
                &Scalar::Z(7.into())
            );
            assert_eq!(
                graph.scalar(original.arguments[1]).unwrap(),
                &Scalar::Z(3.into())
            );
            let mut changed = prefix.to_vec();
            // 唯一の変更は元RuleのLaw span。Scalarの値・args・support・scopeは据え置く。
            changed[reference.0].rule = Rule::Input {
                kind: "law",
                location: Location::Law {
                    span: foreign_ast.span,
                },
            };
            assert_eq!(changed[reference.0].arguments, original.arguments);
            assert_eq!(changed[reference.0].support, original.support);
            assert_eq!(changed[reference.0].scope, original.scope);
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "親Evaluationが未生成の保持prefixでも別ASTへの算術Scalar帰属偽装を拒否する"
            );
            assert!(!original.support.is_empty());
            for change_scope in [false, true] {
                let mut changed = prefix.to_vec();
                if change_scope {
                    changed[reference.0].scope.modes.clear();
                    let mode = if original.scope.modes.contains("observed") {
                        "proposed"
                    } else {
                        "observed"
                    };
                    changed[reference.0].scope.modes.insert(mode.into());
                    assert_ne!(changed[reference.0].scope, original.scope);
                } else {
                    changed[reference.0].support.clear();
                }
                assert!(
                    matches!(
                        rebuild_for_origin_and_support_recheck(&result, &changed),
                        Err(ValidationFailure::Internal(_))
                    ),
                    "親Evaluationを待たず、Scalar自身の支持またはScopeの改変も拒否する"
                );
            }
        }
    }
    #[test]
    fn rejects_selected_reversed_occurrence_in_prefix_with_repeated_total_requests() {
        let original = scalar_operation_private_example(Some(false), Some(true));
        assert_eq!(original.status(), "complete");
        let existing = original.prepared.inputs().sources().clone();
        let old_law = std::str::from_utf8(existing.law().bytes()).unwrap();
        let anchor = "view total(s: State): Z = s.count + s.other;";
        assert_eq!(old_law.matches(anchor).count(), 1);
        let law = old_law.replace(anchor,
        "view total(s: State): Z = s.count + s.other;\n  view reversed(s: State): Z = s.other + s.count;");
        let inputs = InputSources::new(
            existing.definitions().to_vec(),
            super::super::input::InputBytes::new(existing.law().id(), law.into_bytes()),
            existing.archmap().clone(),
        );
        let mut control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        let result = evaluate_observed_bytes(
            inputs,
            &[
                "first=evaluate(CountCheck.reversed,s=@v/s)",
                "one=evaluate(CountCheck.total,s=@v/s)",
                "two=evaluate(CountCheck.total,s=@v/s)",
            ],
            &mut control,
        )
        .expect("三入力の検査と元Request解決を通る正常な同AST反復fixture");
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("同ASTを二度選択した正常全DAGは元入力から再検査できる");
        let first = result.answers.iter().find(|a| a.id == "first").unwrap();
        let one = result.answers.iter().find(|a| a.id == "one").unwrap();
        let two = result.answers.iter().find(|a| a.id == "two").unwrap();
        let foreign = &result.prepared.inputs().law().declarations["CountCheck.reversed"];
        let Signature::View {
            body: foreign_body, ..
        } = &foreign.signature
        else {
            panic!("先行して実評価したview")
        };
        let foreign_span = result.prepared.inputs().law().exprs[*foreign_body].span;
        assert_eq!(
            &result.prepared.inputs().sources().law().bytes()[foreign_span.0..foreign_span.1],
            b"s.other + s.count"
        );
        let total = &result.prepared.inputs().law().declarations["CountCheck.total"];
        let Signature::View {
            body: total_body, ..
        } = &total.signature
        else {
            panic!("二度選択したtotal")
        };
        let ExprKind::Binary {
            op: BinOp::Add,
            lhs,
            ..
        } = &result.prepared.inputs().law().exprs[*total_body].kind
        else {
            panic!("元の加算AST")
        };
        let left_span = result.prepared.inputs().law().exprs[*lhs].span;
        let first_value = first.outputs["value"];
        assert_eq!(graph.scalar(first_value).unwrap(), &Scalar::Z(10.into()));
        assert_eq!(
            graph
                .scalar(result.nodes[first_value.0].arguments[0])
                .unwrap(),
            &Scalar::Z(3.into())
        );
        assert_eq!(
            graph
                .scalar(result.nodes[first_value.0].arguments[1])
                .unwrap(),
            &Scalar::Z(7.into())
        );

        let root_binding = |answer: &Answer| {
            let Some(Payload::Evaluation { expression, .. }) =
                &result.nodes[answer.outputs["evaluation"].0].payload
            else {
                panic!("実Evaluation")
            };
            let Some(Payload::Expression { bindings, .. }) = &result.nodes[expression.0].payload
            else {
                panic!("元total Source")
            };
            assert_eq!(bindings[0].name, "s");
            bindings[0].value
        };
        let one_binding = root_binding(one);
        let two_binding = root_binding(two);
        assert_ne!(
            one_binding, two_binding,
            "同じ明示subjectでも各Requestは異なる表示Refを持つ"
        );
        assert_eq!(
            graph.scalar(one_binding).unwrap(),
            graph.scalar(two_binding).unwrap()
        );

        for answer in [one, two] {
            assert_eq!(answer.status, Decision::Established);
            let reference = answer.outputs["value"];
            let parent = answer.outputs["evaluation"];
            assert!(first_value.0 < reference.0 && reference.0 < parent.0);
            let prefix = &result.nodes[..=reference.0];
            let prefix_graph = rebuild_for_origin_and_support_recheck(&result, prefix)
                .expect("先行reversedや同ASTのSource候補があっても正常な各total prefixは受理する");
            assert!(prefix_graph.get(parent).is_err());
            let original = &prefix[reference.0];
            assert_eq!(
                prefix_graph.scalar(reference).unwrap(),
                &Scalar::Z(10.into())
            );
            assert_eq!(
                prefix_graph.scalar(original.arguments[0]).unwrap(),
                &Scalar::Z(7.into())
            );
            assert_eq!(
                prefix_graph.scalar(original.arguments[1]).unwrap(),
                &Scalar::Z(3.into())
            );
            assert_eq!(original.support, result.nodes[first_value.0].support);
            assert_eq!(original.scope, result.nodes[first_value.0].scope);
            if answer.id == "two" {
                let mut binding_candidates = vec![];
                for node in prefix {
                    if let Some(Payload::Expression {
                        location: Location::Law { span },
                        bindings,
                        ..
                    }) = &node.payload
                        && *span == left_span
                        && !binding_candidates.contains(&bindings[0].value)
                    {
                        binding_candidates.push(bindings[0].value);
                    }
                }
                assert!(
                    binding_candidates.len() >= 2,
                    "同じ左子AST出現に、one/twoの異なる束縛Refを持つSource候補がある"
                );
                assert!(
                    binding_candidates.contains(&one_binding)
                        && binding_candidates.contains(&two_binding)
                );
            }
            let Rule::Input {
                kind: "law",
                location: Location::Law { span },
            } = &original.rule
            else {
                panic!("元totalのLaw Rule")
            };
            assert_ne!(*span, foreign_span);
            let mut changed = prefix.to_vec();
            // 先行選択済みの別ASTは同値10・同支持・同Scopeだが、元の左右は3/7で異なる。
            changed[reference.0].rule = Rule::Input {
                kind: "law",
                location: Location::Law { span: foreign_span },
            };
            assert_eq!(changed[reference.0].arguments, original.arguments);
            assert_eq!(changed[reference.0].support, original.support);
            assert_eq!(changed[reference.0].scope, original.scope);
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "別ASTが選択済みで値/支持/Scopeも一致していても、元child occurrenceと引数Refの帰属偽装を拒否する"
            );
        }
    }

    #[test]
    fn rejects_residual_rule_relabelling_in_an_addition_scalar_prefix() {
        let result = scalar_operation_private_example(Some(false), Some(true));
        assert_eq!(result.status(), "complete");
        let answer = result.answers.iter().find(|a| a.id == "add_zero").unwrap();
        let reference = answer.outputs["value"];
        let parent = answer.outputs["evaluation"];
        assert!(reference.0 < parent.0);
        let prefix = &result.nodes[..=reference.0];
        let graph = rebuild_for_origin_and_support_recheck(&result, prefix)
            .expect("元ASTの生成Scalarまでの正常prefix");
        assert!(graph.get(parent).is_err());
        let original = &prefix[reference.0];
        assert_eq!(graph.scalar(reference).unwrap(), &Scalar::Z(7.into()));
        assert_eq!(original.arguments.len(), 2);
        assert_eq!(
            graph.scalar(original.arguments[0]).unwrap(),
            &Scalar::Z(7.into())
        );
        assert_eq!(
            graph.scalar(original.arguments[1]).unwrap(),
            &Scalar::Z(0.into())
        );
        assert!(matches!(
            &original.rule,
            Rule::Input {
                kind: "law",
                location: Location::Law { .. }
            }
        ));
        let mut changed = prefix.to_vec();
        changed[reference.0].rule = Rule::Construction("evaluation");
        assert_eq!(changed[reference.0].arguments, original.arguments);
        assert_eq!(changed[reference.0].support, original.support);
        assert_eq!(changed[reference.0].scope, original.scope);
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "加算Scalarの保持prefixを残差規則へ付け替えられない"
        );
    }

    fn residual_source_private_example() -> ObservedEvaluation {
        let original = scalar_operation_private_example(Some(false), Some(true));
        assert_eq!(original.status(), "complete");
        let existing = original.prepared.inputs().sources().clone();
        let old_law = std::str::from_utf8(existing.law().bytes()).unwrap();
        let anchor = "law required computed(s: State): s.count + s.other = 10;";
        assert_eq!(old_law.matches(anchor).count(), 1);
        let law = old_law.replace(anchor,
        "law required computed(s: State): s.count + s.other = 10;\n  law required separated(s: State): s.count - s.other = 0;");
        let inputs = InputSources::new(
            existing.definitions().to_vec(),
            super::super::input::InputBytes::new(existing.law().id(), law.into_bytes()),
            existing.archmap().clone(),
        );
        let mut control = Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        });
        evaluate_observed_bytes(
            inputs,
            &[
                "one=check(CountCheck.computed,s=@v/s)",
                "nonzero=check(CountCheck.separated,s=@v/s)",
                "two=check(CountCheck.computed,s=@v/s)",
            ],
            &mut control,
        )
        .expect("同じ三入力定義/観測と有効なZ等式をbyte入口から検査する")
    }

    #[test]
    fn rechecks_residual_source_prefixes_and_rejects_support_scope_or_argument_forgery() {
        let result = residual_source_private_example();
        assert_eq!(result.status(), "complete");
        let whole = rebuild_for_origin_and_support_recheck(&result, &result.nodes)
            .expect("二つの等式と同AST二Requestの全正常DAGを元順で再検査できる");
        let first = result.answers.iter().find(|a| a.id == "one").unwrap();
        let Some(Payload::Evaluation {
            expression: first_source,
            parts: first_parts,
            ..
        }) = &result.nodes[first.outputs["evaluation"].0].payload
        else {
            panic!("最初の等式Evaluation")
        };
        let first_residual = first_parts[0].residual.unwrap();
        let first_left = result.nodes[first_residual.0].arguments[0];
        let Some(Payload::Expression {
            bindings: first_bindings,
            ..
        }) = &result.nodes[first_source.0].payload
        else {
            panic!("最初の等式Source")
        };
        let first_binding = first_bindings[0].value;
        for (id, lhs_value, rhs_value, residual_value, decision) in [
            ("one", 10, 10, 0, Decision::Established),
            ("nonzero", 4, 0, 4, Decision::Refuted),
            ("two", 10, 10, 0, Decision::Established),
        ] {
            let answer = result.answers.iter().find(|a| a.id == id).unwrap();
            assert_eq!(answer.status, decision);
            let parent = answer.outputs["evaluation"];
            let Some(Payload::Evaluation {
                expression,
                bindings,
                parts,
                ..
            }) = &result.nodes[parent.0].payload
            else {
                panic!("元EqのEvaluation")
            };
            let source = *expression;
            let residual = parts[0].residual.expect("既知Z等式は正確な残差を持つ");
            assert!(source.0 < residual.0 && residual.0 < parent.0);
            let prefix = &result.nodes[..=residual.0];
            let graph = rebuild_for_origin_and_support_recheck(&result, prefix)
                .expect("残差Scalar直後で親EqEvaluation未生成の正常prefixを受理する");
            assert!(graph.get(parent).is_err());
            assert_eq!(
                graph.scalar(residual).unwrap(),
                &Scalar::Z(residual_value.into())
            );
            let original = &prefix[residual.0];
            assert!(matches!(&original.rule, Rule::Construction("evaluation")));
            assert_eq!(original.arguments.len(), 2);
            assert_ne!(original.arguments[0], original.arguments[1]);
            assert!(original.arguments.iter().all(|r| r.0 < residual.0));
            assert_eq!(
                graph.scalar(original.arguments[0]).unwrap(),
                &Scalar::Z(lhs_value.into())
            );
            assert_eq!(
                graph.scalar(original.arguments[1]).unwrap(),
                &Scalar::Z(rhs_value.into())
            );
            let Some(Payload::Expression {
                location: Location::Law { span },
                bindings: source_bindings,
                ..
            }) = &prefix[source.0].payload
            else {
                panic!("既出の元Eq Source proof")
            };
            assert_eq!(source_bindings, bindings);
            assert_eq!(bindings[0].name, "s");
            assert!(
                matches!(graph.scalar(bindings[0].value).unwrap(),Scalar::Subject{snapshot,subject,..} if snapshot=="v"&&subject=="s")
            );
            let ast = result
                .prepared
                .inputs()
                .law()
                .exprs
                .iter()
                .find(|e| e.span == *span)
                .unwrap();
            let ExprKind::Binary {
                op: BinOp::Eq,
                lhs,
                rhs,
            } = &ast.kind
            else {
                panic!("残差の元Sourceは実Z等号")
            };
            assert_eq!(
                result.prepared.inputs().law().expr_type(*lhs),
                Some(&Type::Z)
            );
            assert_eq!(
                result.prepared.inputs().law().expr_type(*rhs),
                Some(&Type::Z)
            );
            assert_eq!(parts[0].children.len(), 2);
            for (position, expected_ast) in [*lhs, *rhs].into_iter().enumerate() {
                let child_ref = parts[0].children[position];
                assert!(child_ref.0 < residual.0);
                let Some(Payload::Evaluation {
                    expression,
                    bindings: child_bindings,
                    value: Some(value),
                    ..
                }) = &prefix[child_ref.0].payload
                else {
                    panic!("元lhs/rhsの既知child Evaluation")
                };
                assert_eq!(*value, original.arguments[position]);
                assert_eq!(child_bindings, bindings);
                let Some(Payload::Expression {
                    location: Location::Law { span: child_span },
                    bindings: child_source_bindings,
                    ..
                }) = &prefix[expression.0].payload
                else {
                    panic!("元child Source")
                };
                assert_eq!(
                    *child_span,
                    result.prepared.inputs().law().exprs[expected_ast].span
                );
                assert_eq!(child_source_bindings, bindings);
            }
            for name in ["Counter.State.count", "Counter.State.other"] {
                assert!(original.support.iter().any(|f| f.snapshot == "v"
                    && f.subject == "s"
                    && f.field.as_deref() == Some(name)
                    && f.atom.is_some()));
            }
            assert_eq!(
                original.scope.modes,
                std::collections::BTreeSet::from(["specification".to_owned()])
            );
            assert!(!original.scope.completions);
            for mutate_scope in [false, true] {
                let mut changed = prefix.to_vec();
                if mutate_scope {
                    changed[residual.0].scope.modes =
                        std::collections::BTreeSet::from(["observed".to_owned()]);
                } else {
                    changed[residual.0].support.clear();
                }
                assert_eq!(changed[residual.0].arguments, original.arguments);
                assert!(
                    matches!(
                        rebuild_for_origin_and_support_recheck(&result, &changed),
                        Err(ValidationFailure::Internal(_))
                    ),
                    "残差Scalar自身の実支持またはScopeは親Eqを待たず元Source proofで検査する"
                );
            }
            let mut changed = prefix.to_vec();
            changed[residual.0].arguments.swap(0, 1);
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "数値差が同じ0でも元lhs/rhs childEvalのexact Refを交換できない"
            );
            if id == "two" {
                assert_ne!(first_binding, bindings[0].value);
                assert_eq!(
                    whole.scalar(first_binding).unwrap(),
                    whole.scalar(bindings[0].value).unwrap()
                );
                let mut candidates = vec![];
                for node in prefix {
                    if let Some(Payload::Expression {
                        location:
                            Location::Law {
                                span: candidate_span,
                            },
                        bindings,
                        ..
                    }) = &node.payload
                        && candidate_span == span
                        && !candidates.contains(&bindings[0].value)
                    {
                        candidates.push(bindings[0].value);
                    }
                }
                assert!(
                    candidates.contains(&first_binding) && candidates.contains(&bindings[0].value),
                    "同ASTの複数Source候補があっても正常prefixを受理する"
                );
                assert!(first_left.0 < residual.0 && first_left != original.arguments[0]);
                assert_eq!(
                    whole.scalar(first_left).unwrap(),
                    whole.scalar(original.arguments[0]).unwrap()
                );
                let mut changed = prefix.to_vec();
                changed[residual.0].arguments[0] = first_left;
                assert!(
                    matches!(
                        rebuild_for_origin_and_support_recheck(&result, &changed),
                        Err(ValidationFailure::Internal(_))
                    ),
                    "既出・同値でも別Requestの左子と現在の右子を混ぜた残差proofは拒否する"
                );
            }
        }
    }

    fn numeric_recheck_fixture(omitted: &[&str], body: &str) -> InputSources {
        let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
      "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Numeric","version":"1","dependencies":[],
      "declarations":[{"kind":"entity","name":"Numeric.Sample","meaning":"小さい数値を観測する対象。","parameters":[],
      "fields":[{"name":"q","type":"Q","meaning":"有理数。"},
      {"name":"f","type":["Fp","5"],"meaning":"五元体の値。"},
      {"name":"g","type":["Fp","7"],"meaning":"七元体の値。"},
      {"name":"t","type":["Tuple","Z","Q",["Tuple",["Fp","5"],"Z"]],"meaning":"混合した数値Tuple。"},
      {"name":"p","type":"Bool","meaning":"条件。"}],"alignments":[]}]}]}"#;
        let checked =
            crate::definition::check_definitions(&[("definition0", definitions.as_bytes())])
                .unwrap();
        let digest = &checked.vocabularies["Numeric"].digest;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Calc {{
 use vocabulary Numeric version "1" digest "{digest}";
 {body}
}}
"#
        );
        let atoms = [
        ("q", r#"["-2","3"]"#),
        ("f", r#""4""#),
        ("g", r#""4""#),
        ("t", r#"["-2",["1","2"],["4","3"]]"#),
        ("p", "false"),
    ].into_iter().filter(|(name, _)| !omitted.contains(name)).map(|(name, value)| {
        format!(r#"{{"id":"{name}","subject":"sample","field":"Numeric.Sample.{name}","value":{value},"origin":"values"}}"#)
    }).collect::<Vec<_>>().join(",");
        let map = format!(
            r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Numeric","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"scan","uri":"urn:fixture:numeric-values","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[{{"id":"base","mode":"observed","method":"対象を観測する。","locations":[{{"source":"scan","path":"state.model","span":[0,1]}}]}},
      {{"id":"values","mode":"observed","method":"数値と条件を観測する。","locations":[{{"source":"scan","path":"values.model","span":[2,5]}}]}}],
      "snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Numeric.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
        );
        InputSources::from_bytes(
            vec![definitions.as_bytes().to_vec()],
            law.into_bytes(),
            map.into_bytes(),
        )
    }

    fn numeric_recheck_example() -> ObservedEvaluation {
        evaluate_observed_bytes(
            numeric_recheck_fixture(
                &[],
                r#"
 view q(s: Sample): Q = s.q + rat(5,6);
 view f(s: Sample): Fp(5) = s.f + 3;
 view t(s: Sample): (Z,Q,(Fp(5),Z)) = -s.t;
 view projected(s: Sample): Fp(5) = s.t.2.0;
 view foreign(s: Sample): Q = rat(5,6) + s.q;
 law required equal_q(s: Sample): s.q = rat(1,3);
 law required equal_f(s: Sample): s.f = 1;
 law required equal_t(s: Sample): s.t = (0,rat(1,2),(1,3));
"#,
            ),
            &[
                "foreign=evaluate(Calc.foreign,s=@v/sample)",
                "q=evaluate(Calc.q,s=@v/sample)",
                "f=evaluate(Calc.f,s=@v/sample)",
                "t=evaluate(Calc.t,s=@v/sample)",
                "project=evaluate(Calc.projected,s=@v/sample)",
                "qeq=check(Calc.equal_q,s=@v/sample)",
                "feq=check(Calc.equal_f,s=@v/sample)",
                "teq=check(Calc.equal_t,s=@v/sample)",
                "again=evaluate(Calc.q,s=@v/sample)",
            ],
            &mut Control::unlimited(),
        )
        .unwrap()
    }

    #[test]
    fn rejects_numeric_value_type_normalization_and_producer_substitution_at_prefix() {
        let result = numeric_recheck_example();
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        for (id, false_value) in [
            ("q", Scalar::Q(2.into(), 12.into())),
            (
                "f",
                Scalar::Fp {
                    modulus: "7".into(),
                    value: 2.into(),
                },
            ),
            (
                "t",
                Scalar::Tuple(vec![
                    Scalar::Z(2.into()),
                    Scalar::Q((-1).into(), 2.into()),
                    Scalar::Tuple(vec![
                        Scalar::Fp {
                            modulus: "7".into(),
                            value: 1.into(),
                        },
                        Scalar::Z((-3).into()),
                    ]),
                ]),
            ),
        ] {
            let value = result.answers.iter().find(|a| a.id == id).unwrap().outputs["value"];
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=value.0]).unwrap();
            let mut changed = result.nodes[..=value.0].to_vec();
            let false_type = NodeType::Value(false_value.ty());
            if id != "q" {
                assert_ne!(false_type, result.nodes[value.0].ty);
            }
            changed[value.0].ty = false_type;
            changed[value.0].payload = Some(Payload::Scalar(false_value));
            assert!(matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ));
        }
        let value = result.answers.iter().find(|a| a.id == "q").unwrap().outputs["value"];
        assert_eq!(graph.scalar(value).unwrap(), &Scalar::Q(1.into(), 6.into()));
        let repeated = result
            .answers
            .iter()
            .find(|a| a.id == "again")
            .unwrap()
            .outputs["value"];
        assert_eq!(
            graph.scalar(repeated).unwrap(),
            graph.scalar(value).unwrap()
        );
        assert_ne!(
            result.nodes[repeated.0].arguments,
            result.nodes[value.0].arguments
        );
        let foreign_value = result
            .answers
            .iter()
            .find(|a| a.id == "foreign")
            .unwrap()
            .outputs["value"];
        assert!(foreign_value.0 < value.0);
        assert_eq!(
            graph.scalar(foreign_value).unwrap(),
            graph.scalar(value).unwrap()
        );
        assert_eq!(
            result.nodes[foreign_value.0].support,
            result.nodes[value.0].support
        );
        assert_eq!(
            result.nodes[foreign_value.0].scope,
            result.nodes[value.0].scope
        );
        assert_ne!(
            result.nodes[foreign_value.0].arguments,
            result.nodes[value.0].arguments
        );
        let foreign = &result.prepared.inputs().law().declarations["Calc.foreign"];
        let Signature::View { body, .. } = &foreign.signature else {
            unreachable!()
        };
        let foreign_span = result.prepared.inputs().law().exprs[*body].span;
        assert!(
            matches!(&result.nodes[value.0].rule, Rule::Input { kind: "law", location: Location::Law {span} } if *span != foreign_span)
        );
        assert!(result.nodes[..value.0].iter().any(|node| matches!(&node.payload, Some(Payload::Expression {location: Location::Law {span}, ..}) if *span == foreign_span)));
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=value.0]).unwrap();
        let mut changed = result.nodes[..=value.0].to_vec();
        changed[value.0].rule = Rule::Input {
            kind: "law",
            location: Location::Law { span: foreign_span },
        };
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(&result, &changed),
            Err(ValidationFailure::Internal(_))
        ));
    }

    #[test]
    fn rejects_typed_numeric_residual_and_operand_substitution_at_prefix() {
        let result = numeric_recheck_example();
        assert_eq!(result.status(), "complete");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        for answer in result
            .answers
            .iter()
            .filter(|a| ["qeq", "feq", "teq"].contains(&a.id.as_str()))
        {
            let evaluation = &result.nodes[answer.outputs["evaluation"].0];
            let Some(Payload::Evaluation { parts, .. }) = &evaluation.payload else {
                unreachable!()
            };
            let residual = parts.iter().find_map(|p| p.residual).unwrap();
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=residual.0]).unwrap();
            assert_eq!(
                result.nodes[residual.0].scope.modes,
                ["observed".to_owned()].into()
            );
            for mutation in 0..4 {
                let mut changed = result.nodes[..=residual.0].to_vec();
                match mutation {
                    0 => changed[residual.0].payload = Some(Payload::Scalar(Scalar::Z(0.into()))),
                    1 => changed[residual.0].arguments.swap(0, 1),
                    2 => changed[residual.0].support.clear(),
                    _ => changed[residual.0].scope.modes = ["specification".to_owned()].into(),
                }
                assert!(matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ));
            }
        }
        let value = result.answers.iter().find(|a| a.id == "q").unwrap().outputs["value"];
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=value.0]).unwrap();
        let mut changed = result.nodes[..=value.0].to_vec();
        changed[value.0].arguments.swap(0, 1);
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(&result, &changed),
            Err(ValidationFailure::Internal(_))
        ));
    }

    fn lexical_recheck_example() -> ObservedEvaluation {
        evaluate_observed_bytes(
            numeric_recheck_fixture(
                &[],
                r#"
 view foreign(s: Sample): Q = let other = s.q in other + rat(1,3);
 view bound_value(s: Sample): Q = let x = s.q in x + rat(1,3);
 view foreign_if(s: Sample): Q = if not s.p then s.q else s.q;
 view choice(s: Sample): Q = if s.p then s.q else s.q;
"#,
            ),
            &[
                "foreign=evaluate(Calc.foreign,s=@v/sample)",
                "bound_value=evaluate(Calc.bound_value,s=@v/sample)",
                "again=evaluate(Calc.bound_value,s=@v/sample)",
                "foreign_if=evaluate(Calc.foreign_if,s=@v/sample)",
                "choice=evaluate(Calc.choice,s=@v/sample)",
            ],
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    fn lexical_alias_evaluation(result: &ObservedEvaluation, answer_id: &str) -> NodeRef {
        let answer = result.answers.iter().find(|a| a.id == answer_id).unwrap();
        let Some(Payload::Evaluation {
            bindings: expected, ..
        }) = &result.nodes[answer.outputs["evaluation"].0].payload
        else {
            unreachable!()
        };
        result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(i, node)| {
                let Some(Payload::Evaluation {
                    expression,
                    bindings,
                    parts,
                    ..
                }) = &node.payload
                else {
                    return None;
                };
                let Some(Payload::Expression {
                    location: Location::Law { span },
                    ..
                }) = &result.nodes[expression.0].payload
                else {
                    return None;
                };
                (bindings == expected
                    && !parts[0].children.is_empty()
                    && &result.prepared.inputs().sources().law().bytes()[span.0..span.1] == b"x")
                    .then_some(NodeRef(i))
            })
            .unwrap()
    }

    #[test]
    fn rejects_lexical_rhs_alias_request_and_producer_substitution_at_prefix() {
        let result = lexical_recheck_example();
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let local = result
            .answers
            .iter()
            .find(|a| a.id == "bound_value")
            .unwrap()
            .outputs["value"];
        let foreign = result
            .answers
            .iter()
            .find(|a| a.id == "foreign")
            .unwrap()
            .outputs["value"];
        assert!(foreign.0 < local.0);
        assert_eq!(graph.scalar(local).unwrap(), graph.scalar(foreign).unwrap());
        assert_eq!(
            result.nodes[local.0].support,
            result.nodes[foreign.0].support
        );
        assert_eq!(result.nodes[local.0].scope, result.nodes[foreign.0].scope);
        let (
            Rule::Input {
                kind: "law",
                location: Location::Law { span: own_span },
            },
            Rule::Input {
                kind: "law",
                location: Location::Law { span: foreign_span },
            },
        ) = (&result.nodes[local.0].rule, &result.nodes[foreign.0].rule)
        else {
            unreachable!()
        };
        assert_ne!(own_span, foreign_span);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=local.0]).unwrap();
        for mutation in 0..4 {
            let mut changed = result.nodes[..=local.0].to_vec();
            match mutation {
                0 => changed[local.0].rule = result.nodes[foreign.0].rule.clone(),
                1 => changed[local.0].arguments[0] = result.nodes[foreign.0].arguments[0],
                2 => changed[local.0].support.clear(),
                _ => changed[local.0].scope.modes = ["specification".to_owned()].into(),
            }
            assert!(matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ));
        }
        let earlier = lexical_alias_evaluation(&result, "bound_value");
        let later = lexical_alias_evaluation(&result, "again");
        let Some(Payload::Evaluation {
            bindings: earlier_bindings,
            parts: earlier_parts,
            value: earlier_value,
            ..
        }) = &result.nodes[earlier.0].payload
        else {
            unreachable!()
        };
        let Some(Payload::Evaluation {
            bindings: later_bindings,
            parts: later_parts,
            value: later_value,
            ..
        }) = &result.nodes[later.0].payload
        else {
            unreachable!()
        };
        assert!(earlier_parts[0].children[0].0 < later.0);
        assert_ne!(earlier_bindings, later_bindings);
        assert_ne!(earlier_parts[0].children, later_parts[0].children);
        assert_eq!(
            graph.scalar(earlier_value.unwrap()).unwrap(),
            graph.scalar(later_value.unwrap()).unwrap()
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=later.0]).unwrap();
        let mut changed = result.nodes[..=later.0].to_vec();
        let Some(Payload::Evaluation {
            expression,
            parts,
            value,
            ..
        }) = &mut changed[later.0].payload
        else {
            unreachable!()
        };
        parts[0].children = earlier_parts[0].children.clone();
        parts[0].value = *earlier_value;
        *value = *earlier_value;
        let arguments = std::iter::once(*expression)
            .chain(earlier_parts[0].children.iter().copied())
            .chain(*earlier_value)
            .collect();
        changed[later.0].arguments = arguments;
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(&result, &changed),
            Err(ValidationFailure::Internal(_))
        ));
    }

    #[test]
    fn rejects_if_condition_branch_order_value_and_scope_substitution_at_prefix() {
        let result = lexical_recheck_example();
        assert_eq!(result.status(), "complete");
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let value = result
            .answers
            .iter()
            .find(|a| a.id == "choice")
            .unwrap()
            .outputs["value"];
        let foreign = result
            .answers
            .iter()
            .find(|a| a.id == "foreign_if")
            .unwrap()
            .outputs["value"];
        assert!(foreign.0 < value.0);
        assert_eq!(graph.scalar(value).unwrap(), graph.scalar(foreign).unwrap());
        assert_eq!(
            result.nodes[value.0].support,
            result.nodes[foreign.0].support
        );
        assert_eq!(result.nodes[value.0].scope, result.nodes[foreign.0].scope);
        let (
            Rule::Input {
                kind: "law",
                location: Location::Law { span: own_span },
            },
            Rule::Input {
                kind: "law",
                location: Location::Law { span: foreign_span },
            },
        ) = (&result.nodes[value.0].rule, &result.nodes[foreign.0].rule)
        else {
            unreachable!()
        };
        assert_ne!(own_span, foreign_span);
        assert_ne!(
            result.nodes[value.0].arguments[1],
            result.nodes[value.0].arguments[2]
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=value.0]).unwrap();
        for mutation in 0..6 {
            let mut changed = result.nodes[..=value.0].to_vec();
            match mutation {
                0 => changed[value.0].rule = result.nodes[foreign.0].rule.clone(),
                1 => changed[value.0].arguments[0] = result.nodes[foreign.0].arguments[0],
                2 => changed[value.0].arguments.swap(1, 2),
                3 => {
                    changed[value.0].payload = Some(Payload::Scalar(Scalar::Q(0.into(), 1.into())))
                }
                4 => changed[value.0].support.clear(),
                _ => changed[value.0].scope.modes = ["specification".to_owned()].into(),
            }
            assert!(matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ));
        }
    }

    #[test]
    fn rejects_unknown_let_if_value_and_fabricated_lexical_binding() {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(
                &["q", "p"],
                r#"
 view dependent(s: Sample): Q = let x = s.q in x + 1;
 view conditional(s: Sample): Q = if s.p then 2 else 3;
"#,
            ),
            &[
                "dependent=evaluate(Calc.dependent,s=@v/sample)",
                "conditional=evaluate(Calc.conditional,s=@v/sample)",
            ],
            &mut Control::unlimited(),
        )
        .unwrap();
        assert_eq!(result.status(), "partial");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        for answer in &result.answers {
            assert!(!answer.outputs.contains_key("value"));
            let root = answer.outputs["evaluation"];
            let node = &result.nodes[root.0];
            let Some(Payload::Evaluation {
                expression,
                parts,
                value,
                ..
            }) = &node.payload
            else {
                unreachable!()
            };
            assert!(value.is_none());
            let Some(Payload::Expression { location, .. }) = &result.nodes[expression.0].payload
            else {
                unreachable!()
            };
            let mut prefix = result.nodes[..root.0].to_vec();
            rebuild_for_origin_and_support_recheck(&result, &prefix).unwrap();
            prefix.push(Node {
                ty: NodeType::Value(Type::Q),
                payload: Some(Payload::Scalar(Scalar::Q(0.into(), 1.into()))),
                rule: Rule::Input {
                    kind: "law",
                    location: location.clone(),
                },
                arguments: parts[0].children.clone(),
                support: node.support.clone(),
                scope: node.scope.clone(),
                evidence: vec![],
                judgment: None,
                reasons: vec![],
            });
            assert!(matches!(
                rebuild_for_origin_and_support_recheck(&result, &prefix),
                Err(ValidationFailure::Internal(_))
            ));
        }
        let alias = lexical_alias_evaluation(&result, "dependent");
        let Some(Payload::Evaluation { expression, .. }) = &result.nodes[alias.0].payload else {
            unreachable!()
        };
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=expression.0]).unwrap();
        let mut changed = result.nodes[..=expression.0].to_vec();
        let Some(Payload::Expression { bindings, .. }) = &mut changed[expression.0].payload else {
            unreachable!()
        };
        let subject = bindings[0].clone();
        bindings.push(Binding {
            name: "x".into(),
            value: subject.value,
            ty: subject.ty,
        });
        changed[expression.0].arguments.push(subject.value);
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(&result, &changed),
            Err(ValidationFailure::Internal(_))
        ));
    }

    #[test]
    fn rejects_lexical_use_relocated_to_field_or_comment_token_at_prefix() {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(
                &[],
                "view token_case(s: Sample): Q = let q = rat(5,7) in q + // q\n s.q;",
            ),
            &["token=evaluate(Calc.token_case,s=@v/sample)"],
            &mut Control::unlimited(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let law = result.prepared.inputs().law();
        let bytes = result.prepared.inputs().sources().law().bytes();
        let (alias, source, original_span) = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                let Some(Payload::Evaluation {
                    expression, parts, ..
                }) = &node.payload
                else {
                    return None;
                };
                let Some(Payload::Expression {
                    location: Location::Law { span },
                    ..
                }) = &result.nodes[expression.0].payload
                else {
                    return None;
                };
                (&bytes[span.0..span.1] == b"q" && parts[0].children.len() == 1).then_some((
                    NodeRef(index),
                    *expression,
                    *span,
                ))
            })
            .unwrap();
        let field_span = law
            .exprs
            .iter()
            .find_map(|e| match &e.kind {
                ExprKind::Dotted(parts)
                    if parts.len() == 2 && parts[0].name == "s" && parts[1].name == "q" =>
                {
                    Some(parts[1].span)
                }
                _ => None,
            })
            .unwrap();
        let comment_start = bytes.windows(4).position(|w| w == b"// q").unwrap() + 3;
        let comment_span = (comment_start, comment_start + 1);
        assert!(source.0 < alias.0);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source.0]).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=alias.0]).unwrap();
        for false_span in [field_span, comment_span] {
            assert_ne!(false_span, original_span);
            assert_eq!(&bytes[false_span.0..false_span.1], b"q");
            assert!(
                !law.exprs
                    .iter()
                    .enumerate()
                    .any(|(id, e)| law.expr_type(id).is_some() && e.span == false_span)
            );
            assert!(!law.exprs.iter().enumerate().any(|(id,e)| law.expr_type(id).is_some() && matches!(&e.kind,ExprKind::Dotted(parts) if parts[0].span == false_span)));
            let mut changed = result.nodes[..=alias.0].to_vec();
            let Some(Payload::Expression { location, .. }) = &mut changed[source.0].payload else {
                unreachable!()
            };
            *location = Location::Law { span: false_span };
            changed[source.0].rule = Rule::Input {
                kind: "law",
                location: Location::Law { span: false_span },
            };
            let Some(Payload::Evaluation { parts, .. }) = &mut changed[alias.0].payload else {
                unreachable!()
            };
            parts[0].location = Location::Law { span: false_span };
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "同綴りのfield名/コメントをlexical使用出現へ付替えたprefixを拒否する"
            );
        }
    }

    #[test]
    fn rejects_missing_lexical_source_with_invented_free_parameter_at_prefix() {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(
                &["q"],
                "view dependent(s: Sample): Q = let x = s.q in x + 1;",
            ),
            &["dependent=evaluate(Calc.dependent,s=@v/sample)"],
            &mut Control::unlimited(),
        )
        .unwrap();
        assert_eq!(result.status(), "partial");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let alias = lexical_alias_evaluation(&result, "dependent");
        let Some(Payload::Evaluation {
            expression, value, ..
        }) = &result.nodes[alias.0].payload
        else {
            unreachable!()
        };
        assert!(value.is_none());
        assert!(result.nodes[expression.0].scope.completions);
        let Some(Payload::Expression {
            parameters,
            bindings,
            ..
        }) = &result.nodes[expression.0].payload
        else {
            unreachable!()
        };
        assert!(parameters.is_empty());
        assert_eq!(
            bindings.iter().map(|b| b.name.as_str()).collect::<Vec<_>>(),
            vec!["s"]
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=expression.0]).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=alias.0]).unwrap();
        let mut changed = result.nodes[..=expression.0].to_vec();
        let Some(Payload::Expression { parameters, .. }) = &mut changed[expression.0].payload
        else {
            unreachable!()
        };
        parameters.push(("x".into(), Type::Q));
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&result, &changed),
                Err(ValidationFailure::Internal(_))
            ),
            "元の欠測lexical名を新たな自由parameterに変更したSourceを拒否する"
        );
    }
    fn named_call_quiet() -> Control {
        Control::new(super::super::control::Limits::default(), |_| {
            super::super::control::Usage::default()
        })
    }
    #[test]
    fn named_calls_reject_out_of_range_request_at_root_source_prefix() {
        let mut result = evaluate_observed_bytes(
            numeric_recheck_fixture(&[], "view one(): Z = 1; view zero(): Z = one();"),
            &["v=evaluate(Calc.zero)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete");
        assert_eq!(result.contexts[0].request, 0);
        assert_eq!(result.contexts[0].frame, None);
        assert!(matches!(
            &result.nodes[0].payload,
            Some(Payload::Expression { .. })
        ));
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..1]).unwrap();

        result.contexts[0].request = usize::MAX;
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..1]),
            Err(ValidationFailure::Internal(_))
        ));
    }
    fn named_call_private_example(omitted: &[&str]) -> ObservedEvaluation {
        evaluate_observed_bytes(
            numeric_recheck_fixture(
                omitted,
                r#"
 view combine(x: Q, y: Q): Q = x + y;
 view retain(x: Q): Q = x;
 view unused(x: Q): Q = 7;
 view read(s: Sample): Q = s.q;
 view caller(s: Sample): Q = combine(s.q, s.q) + retain(s.q);
 view field(s: Sample): Q = read(s);
 view unknown(s: Sample): Q = retain(s.q);
 view constant(s: Sample): Q = unused(s.q);
"#,
            ),
            if omitted.is_empty() {
                &[
                    "first=evaluate(Calc.caller,s=@v/sample)",
                    "again=evaluate(Calc.caller,s=@v/sample)",
                    "field=evaluate(Calc.field,s=@v/sample)",
                ]
            } else {
                &[
                    "unknown=evaluate(Calc.unknown,s=@v/sample)",
                    "constant=evaluate(Calc.constant,s=@v/sample)",
                ]
            },
            &mut named_call_quiet(),
        )
        .unwrap()
    }
    fn named_body(result: &ObservedEvaluation, frame: usize) -> usize {
        result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (result.contexts[index].frame == Some(frame)
                    && matches!(&node.payload, Some(Payload::Expression { .. })))
                .then_some(index)
            })
            .unwrap()
    }
    fn rejects_named_prefix(result: &ObservedEvaluation, nodes: &[Node]) {
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(result, nodes),
            Err(ValidationFailure::Internal(_))
        ));
    }
    #[test]
    fn named_calls_recheck_full_and_prefix_sources_body_and_equal_producers() {
        let result = named_call_private_example(&[]);
        assert_eq!(result.status(), "complete");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let sum_frame = result
            .frames
            .iter()
            .enumerate()
            .find_map(|(index, frame)| {
                let Some(Payload::Expression {
                    location: Location::Law { span },
                    ..
                }) = &result.nodes[frame.source.0].payload
                else {
                    return None;
                };
                (std::str::from_utf8(
                    &result.prepared.inputs().sources().law().bytes()[span.0..span.1],
                )
                .unwrap()
                    == "combine(s.q, s.q)")
                    .then_some(index)
            })
            .unwrap();
        let source = named_body(&result, sum_frame);
        let source_node = &result.nodes[source];
        assert_eq!(source_node.scope.readings, ["Calc".to_owned()].into());
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source]).unwrap();
        let mut changed = result.nodes[..=source].to_vec();
        changed[source]
            .support
            .push(result.nodes[result.frames[sum_frame].arguments[0].0].support[0].clone());
        rejects_named_prefix(&result, &changed);
        let mut changed = result.nodes[..=source].to_vec();
        changed[source].scope.readings.insert("Foreign".into());
        rejects_named_prefix(&result, &changed);
        let mut changed = result.nodes[..=source].to_vec();
        if let Some(Payload::Expression { bindings, .. }) = &mut changed[source].payload {
            bindings[0].name = "other".into();
        }
        rejects_named_prefix(&result, &changed);
        let mut changed = result.nodes[..=source].to_vec();
        if let Some(Payload::Expression { bindings, .. }) = &mut changed[source].payload {
            bindings[0].ty = Type::Z;
        }
        rejects_named_prefix(&result, &changed);
        let mut changed = result.nodes[..=source].to_vec();
        if let Some(Payload::Expression { parameters, .. }) = &mut changed[source].payload {
            parameters.push(("free".into(), Type::Q));
        }
        rejects_named_prefix(&result, &changed);
        let foreign = result
            .prepared
            .inputs()
            .law()
            .declarations
            .get("Calc.retain")
            .unwrap();
        let Signature::View {
            body: foreign_body, ..
        } = &foreign.signature
        else {
            unreachable!()
        };
        let foreign_span = result.prepared.inputs().law().exprs[*foreign_body].span;
        let mut changed = result.nodes[..=source].to_vec();
        if let Some(Payload::Expression { location, .. }) = &mut changed[source].payload {
            *location = Location::Law { span: foreign_span };
        }
        rejects_named_prefix(&result, &changed);
        let arithmetic = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (result.contexts[index].frame == Some(sum_frame)
                    && matches!(&node.payload, Some(Payload::Scalar(Scalar::Q(_, _)))))
                .then_some(index)
            })
            .unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=arithmetic]).unwrap();
        assert_eq!(result.nodes[arithmetic].arguments.len(), 2);
        assert_ne!(
            result.nodes[arithmetic].arguments[0],
            result.nodes[arithmetic].arguments[1]
        );
        let mut changed = result.nodes[..=arithmetic].to_vec();
        changed[arithmetic].arguments[0] = changed[arithmetic].arguments[1];
        rejects_named_prefix(&result, &changed);
        let call_value = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (result.contexts[index] == result.frames[sum_frame].caller
                    && matches!(&node.payload, Some(Payload::Scalar(_)))
                    && node
                        .arguments
                        .last()
                        .is_some_and(|r| result.contexts[r.0].frame == Some(sum_frame)))
                .then_some(index)
            })
            .unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=call_value]).unwrap();
        let mut changed = result.nodes[..=call_value].to_vec();
        changed[call_value].arguments.swap(0, 1);
        rejects_named_prefix(&result, &changed);
        let mut changed = result.nodes.clone();
        changed[call_value].arguments.swap(0, 1);
        rejects_named_prefix(&result, &changed);
    }
    #[test]
    fn named_calls_recheck_original_call_argument_order_frame_and_request() {
        let mut result = named_call_private_example(&[]);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let later = result
            .frames
            .iter()
            .enumerate()
            .find_map(|(index, frame)| (frame.caller.request == 1).then_some(index))
            .unwrap();
        let source = named_body(&result, later);
        let original_context = result.contexts[source];
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source]).unwrap();
        result.contexts[source].frame = Some(0);
        rejects_named_prefix(&result, &result.nodes[..=source]);
        result.contexts[source] = original_context;
        result.contexts[source].request = 0;
        rejects_named_prefix(&result, &result.nodes[..=source]);
        result.contexts[source] = original_context;
        let original = result.frames[later].clone();
        result.frames[later].source = result.frames[0].source;
        rejects_named_prefix(&result, &result.nodes[..=source]);
        result.frames[later] = original.clone();
        result.frames[later].arguments.swap(0, 1);
        rejects_named_prefix(&result, &result.nodes[..=source]);
        result.frames[later] = original.clone();
        result.frames[later].caller.request = 0;
        rejects_named_prefix(&result, &result.nodes[..=source]);
        result.frames[later] = original;
        let mut changed = result.nodes[..=source].to_vec();
        changed[source].arguments.pop();
        rejects_named_prefix(&result, &changed);
        let argument = result.frames[later].arguments[0];
        let Some(Payload::Evaluation { parts, .. }) = &result.nodes[argument.0].payload else {
            unreachable!()
        };
        let arg_value = parts[0].value.unwrap();
        let prior = result.frames[0].arguments[0];
        let Some(Payload::Evaluation {
            value: Some(prior_value),
            ..
        }) = &result.nodes[prior.0].payload
        else {
            unreachable!()
        };
        assert_ne!(arg_value, *prior_value);
        let mut changed = result.nodes[..=source].to_vec();
        if let Some(Payload::Expression { bindings, .. }) = &mut changed[source].payload {
            bindings[0].value = *prior_value;
        }
        rejects_named_prefix(&result, &changed);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
    #[test]
    fn named_calls_keep_missing_formals_as_argument_evaluations_in_prefixes() {
        let result = named_call_private_example(&["q"]);
        assert_eq!(result.status(), "partial");
        assert!(!result.answers[0].outputs.contains_key("value"));
        assert!(result.answers[1].outputs.contains_key("value"));
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        for frame in 0..result.frames.len() {
            let source = named_body(&result, frame);
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source]).unwrap();
            let Some(Payload::Expression {
                parameters,
                bindings,
                ..
            }) = &result.nodes[source].payload
            else {
                unreachable!()
            };
            assert!(parameters.is_empty() && bindings.is_empty());
            assert_eq!(
                result.nodes[source].arguments,
                vec![
                    result.frames[frame].source,
                    result.frames[frame].arguments[0]
                ]
            );
            let mut changed = result.nodes[..=source].to_vec();
            if let Some(Payload::Expression { parameters, .. }) = &mut changed[source].payload {
                parameters.push(("x".into(), Type::Q));
            }
            rejects_named_prefix(&result, &changed);
        }
        let missing_name = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (result.contexts[index].frame == Some(0)
                    && matches!(&node.payload, Some(Payload::Evaluation { value: None, .. })))
                .then_some(index)
            })
            .unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=missing_name]).unwrap();
        let mut changed = result.nodes[..=missing_name].to_vec();
        if let Some(Payload::Evaluation { parts, .. }) = &mut changed[missing_name].payload {
            parts[0].children.clear();
        }
        rejects_named_prefix(&result, &changed);
    }
    #[test]
    fn named_call_validation_success_is_not_reused_after_same_environment_forgery() {
        let result = named_call_private_example(&[]);
        let mut control = named_call_quiet();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let mut graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let index = named_body(&result, 0);
        let normal = graph.nodes[index].clone();
        // 同じEnvironment、同じGraph、同じindexの正常照合を先に確定する。
        environment
            .recheck_node(&graph, &graph.nodes[index], index)
            .unwrap();
        graph.nodes[index].scope.readings.insert("Foreign".into());
        assert!(matches!(
            environment.recheck_node(&graph, &graph.nodes[index], index),
            Err(ValidationFailure::Internal(_))
        ));
        graph.nodes[index] = normal.clone();
        environment
            .recheck_node(&graph, &graph.nodes[index], index)
            .unwrap();
        // 元nodeと異なるcloneも、直前の成功indexで照合を省略できない。
        let mut forged = normal;
        if let Some(Payload::Expression { bindings, .. }) = &mut forged.payload {
            bindings[0].name = "foreign".into();
        }
        assert!(matches!(
            environment.recheck_node(&graph, &forged, index),
            Err(ValidationFailure::Internal(_))
        ));
        environment
            .recheck_node(&graph, &graph.nodes[index], index)
            .unwrap();
    }
    #[test]
    fn named_calls_keep_unknown_ref_field_as_not_implemented_at_callee_source() {
        fn inputs(unknown: bool) -> InputSources {
            let sources = numeric_recheck_fixture(
                if unknown { &["p"] } else { &[] },
                r#"
 view read(x: Sample): Q = x.q;
 view caller(s: Sample, t: Sample): Q = read(if s.p then t else s);
"#,
            );
            let map = std::str::from_utf8(sources.archmap().bytes()).unwrap().replace(
                r#"{"id":"sample","type":"Numeric.Sample","origin":"base"}"#,
                r#"{"id":"sample","type":"Numeric.Sample","origin":"base"},{"id":"other","type":"Numeric.Sample","origin":"base"}"#,
            );
            InputSources::from_bytes(
                sources
                    .definitions()
                    .iter()
                    .map(|s| s.bytes().to_vec())
                    .collect(),
                sources.law().bytes().to_vec(),
                map.into_bytes(),
            )
        }
        let normal = evaluate_observed_bytes(
            inputs(false),
            &["v=evaluate(Calc.caller,s=@v/sample,t=@v/other)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(normal.status(), "complete");
        assert!(
            matches!(&normal.nodes[normal.answers[0].outputs["value"].0].payload, Some(Payload::Scalar(Scalar::Q(n,d))) if n == &(-2).into() && d == &3.into())
        );
        let sources = inputs(true);
        let law = sources.law().bytes().to_vec();
        let failure = evaluate_observed_bytes(
            sources,
            &["v=evaluate(Calc.caller,s=@v/sample,t=@v/other)"],
            &mut named_call_quiet(),
        )
        .unwrap_err();
        assert!(failure.wire().is_none());
        let EvaluationFailure::NotImplemented {
            location: Location::Law { span },
            feature,
            ..
        } = failure
        else {
            panic!("未知Ref fieldをInternalへ変えない");
        };
        assert_eq!(&law[span.0..span.1], b"x.q");
        assert_eq!(feature, "未確定の参照からの field 読取り");
    }
    #[test]
    fn named_calls_reject_equal_literal_and_field_scalars_from_another_call_frame() {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(
                &[],
                r#"
 view pure(): Q = 1;
 view read(s: Sample): Q = s.q;
 view caller(s: Sample): Q = pure()+pure()+read(s)+read(s);
"#,
            ),
            &["v=evaluate(Calc.caller,s=@v/sample)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        assert_eq!(result.frames.len(), 4);
        for (earlier, later) in [(0, 1), (2, 3)] {
            let scalar = |frame| {
                result
                    .nodes
                    .iter()
                    .enumerate()
                    .find_map(|(index, node)| {
                        (result.contexts[index].frame == Some(frame)
                            && matches!(&node.payload, Some(Payload::Scalar(Scalar::Q(_, _)))))
                        .then_some(NodeRef(index))
                    })
                    .unwrap()
            };
            let (earlier_scalar, later_scalar) = (scalar(earlier), scalar(later));
            assert_ne!(earlier_scalar, later_scalar);
            assert_eq!(
                result.nodes[earlier_scalar.0].scope,
                result.nodes[later_scalar.0].scope
            );
            assert!(
                matches!((&result.nodes[earlier_scalar.0].payload, &result.nodes[later_scalar.0].payload), (Some(Payload::Scalar(a)), Some(Payload::Scalar(b))) if a == b)
            );
            let evaluation = result.nodes.iter().enumerate().find_map(|(index, node)| (result.contexts[index].frame == Some(later) && matches!(&node.payload, Some(Payload::Evaluation { value: Some(value), .. }) if *value == later_scalar)).then_some(index)).unwrap();
            // 同じ論理結果edgeのwire上の重複表示を揃え、構造不整合では拒否させない。
            let replace = |nodes: &mut [Node]| {
                let node = &mut nodes[evaluation];
                if let Some(Payload::Evaluation { value, parts, .. }) = &mut node.payload {
                    *value = Some(earlier_scalar);
                    parts[0].value = Some(earlier_scalar);
                }
                for argument in &mut node.arguments {
                    if *argument == later_scalar {
                        *argument = earlier_scalar;
                    }
                }
            };
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=evaluation]).unwrap();
            let mut prefix = result.nodes[..=evaluation].to_vec();
            replace(&mut prefix);
            rejects_named_prefix(&result, &prefix);
            let mut full = result.nodes.clone();
            replace(&mut full);
            rejects_named_prefix(&result, &full);
        }
    }
    #[test]
    fn named_calls_keep_unimplemented_callee_forms_distinct_from_internal_failure() {
        let normal = evaluate_observed_bytes(
            numeric_recheck_fixture(
                &[],
                r#"
 view retain(x: Bool): (Bool,Bool) = (x,x);
 view caller(s: Sample): (Bool,Bool) = retain(s.p);
"#,
            ),
            &["v=evaluate(Calc.caller,s=@v/sample)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(normal.status(), "complete");
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        let value = data_scalar_at(&normal, normal.answers[0].outputs["value"].0);
        assert_eq!(value.ty(), Type::Tuple(vec![Type::Bool, Type::Bool]));
        assert_eq!(
            value,
            &Scalar::Tuple(vec![Scalar::Bool(false), Scalar::Bool(false)])
        );
        let sources = numeric_recheck_fixture(
            &[],
            r#"
 view unsupported(s: Sample): Bool = forall item: Bool. item;
 view caller(s: Sample): Bool = unsupported(s);
"#,
        );
        let law = sources.law().bytes().to_vec();
        let failure = evaluate_observed_bytes(
            sources,
            &["v=evaluate(Calc.caller,s=@v/sample)"],
            &mut named_call_quiet(),
        )
        .unwrap_err();
        assert!(failure.wire().is_none());
        let EvaluationFailure::NotImplemented {
            location: Location::Law { span },
            ..
        } = failure
        else {
            panic!("範囲外のcallee式は専用未実装を保つ");
        };
        assert_eq!(&law[span.0..span.1], b"forall item: Bool. item");
    }
    #[test]
    fn named_calls_reject_equal_atom_from_another_field_at_scalar_prefix() {
        let original = numeric_recheck_fixture(
            &[],
            r#"
 view read(x: Sample): Q = x.q;
 view caller(s: Sample): Q = read(s);
"#,
        );
        let original_definition = std::str::from_utf8(original.definitions()[0].bytes()).unwrap();
        let definition = original_definition.replace(
            r#"{"name":"q","type":"Q","meaning":"有理数。"}"#,
            r#"{"name":"q","type":"Q","meaning":"有理数。"},{"name":"q2","type":"Q","meaning":"別の有理数。"}"#,
        );
        assert_ne!(definition, original_definition);
        let old = crate::definition::check_definitions_controlled(
            &[("definition0", original_definition.as_bytes())],
            &mut named_call_quiet(),
        )
        .unwrap();
        let new = crate::definition::check_definitions_controlled(
            &[("definition0", definition.as_bytes())],
            &mut named_call_quiet(),
        )
        .unwrap();
        let (old_digest, new_digest) = (
            &old.vocabularies["Numeric"].digest,
            &new.vocabularies["Numeric"].digest,
        );
        let law = std::str::from_utf8(original.law().bytes())
            .unwrap()
            .replace(old_digest, new_digest);
        let map = std::str::from_utf8(original.archmap().bytes()).unwrap().replace(old_digest, new_digest).replace(
            r#""atoms":["#,
            r#""atoms":[{"id":"q2","subject":"sample","field":"Numeric.Sample.q2","value":["-2","3"],"origin":"values"},"#,
        );
        let result = evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![definition.into_bytes()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &["v=evaluate(Calc.caller,s=@v/sample)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let scalar = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (result.contexts[index].frame == Some(0)
                    && matches!(&node.payload, Some(Payload::Scalar(Scalar::Q(_, _)))))
                .then_some(index)
            })
            .unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
        let field = result.prepared.inputs().archmap().snapshots[0].subjects[0]
            .fields
            .iter()
            .find(|f| f.name == "Numeric.Sample.q2")
            .unwrap();
        let Slot::Known { pointer, atom, .. } = &field.slot else {
            unreachable!()
        };
        let mut changed = result.nodes[..=scalar].to_vec();
        changed[scalar].rule = Rule::Input {
            kind: "atom",
            location: Location::ArchMap {
                pointer: pointer.clone(),
                span: None,
            },
        };
        changed[scalar].support = vec![Fact {
            snapshot: "v".into(),
            subject: "sample".into(),
            field: Some(field.name.clone()),
            atom: Some(atom.clone()),
        }];
        // 同型同値・同owner・同Scopeでも、元callee field x.qをq2へ変えない。
        rejects_named_prefix(&result, &changed);
    }
    #[test]
    fn named_calls_read_distinct_field_names_from_two_ref_entity_types() {
        let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
 "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Owners","version":"1","dependencies":[],"declarations":[
 {"kind":"entity","name":"Owners.First","meaning":"第一の対象。","parameters":[],"fields":[{"name":"a","type":"Q","meaning":"第一の値。"}],"alignments":[]},
 {"kind":"entity","name":"Owners.Second","meaning":"第二の対象。","parameters":[],"fields":[{"name":"b","type":"Q","meaning":"第二の値。"}],"alignments":[]}]}]}"#;
        let checked = crate::definition::check_definitions_controlled(
            &[("definition0", definitions.as_bytes())],
            &mut named_call_quiet(),
        )
        .unwrap();
        let digest = &checked.vocabularies["Owners"].digest;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
 reading Calc {{ use vocabulary Owners version "1" digest "{digest}";
 view read(x: First, y: Second): Q = x.a+y.b;
 view caller(x: First, y: Second): Q = read(x,y);
 }}"#
        );
        let map = format!(
            r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
 "vocabularies":[{{"namespace":"Owners","version":"1","digest":"{digest}"}}],
 "sources":[{{"id":"scan","uri":"urn:fixture:two-field-owners","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
 "origins":[{{"id":"base","mode":"observed","method":"二つの対象を観測する。","locations":[{{"source":"scan","path":"two-owners.model","span":[0,2]}}]}}],
 "snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"first","type":"Owners.First","origin":"base"}},{{"id":"second","type":"Owners.Second","origin":"base"}}],
 "atoms":[{{"id":"a","subject":"first","field":"Owners.First.a","value":["1","2"],"origin":"base"}},{{"id":"b","subject":"second","field":"Owners.Second.b","value":["1","3"],"origin":"base"}}]}}]}}"#
        );
        let result = evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![definitions.as_bytes().to_vec()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &["v=evaluate(Calc.caller,x=@v/first,y=@v/second)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(
            result.status(),
            "complete",
            "異なるownerの無関係field候補で失敗しない: {:?}",
            result.issues
        );
        let value = result.answers[0].outputs["value"];
        assert!(
            matches!(&result.nodes[value.0].payload, Some(Payload::Scalar(Scalar::Q(n,d))) if n == &5.into() && d == &6.into())
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let scalar = result.nodes.iter().enumerate().find_map(|(index, node)| (result.contexts[index].frame == Some(0) && matches!(&node.rule, Rule::Input {kind: "atom", location: Location::ArchMap {pointer, ..}} if pointer.ends_with("/atoms/1/value"))).then_some(index)).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
    }
    #[test]
    fn named_parameter_name_token_checkpoint_preserves_original_stop_through_driver() {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{
            cell::{Cell, RefCell},
            rc::Rc,
        };
        let sources = numeric_recheck_fixture(
            &["p"],
            r#"
 view retain(x: Bool): Bool = x;
 view seed(s: Sample): Q = s.q;
 view missing(s: Sample): Bool = s.p;
 view current(s: Sample): Bool = retain(s.p);
 view later(s: Sample): Q = s.q;
"#,
        );
        let asks = [
            "seed=evaluate(Calc.seed,s=@v/sample)",
            "missing=evaluate(Calc.missing,s=@v/sample)",
            "current=evaluate(Calc.current,s=@v/sample)",
            "later=evaluate(Calc.later,s=@v/sample)",
        ];
        let mut baseline_control = named_call_quiet();
        let prepared = prepare_observed(sources.clone(), &asks, &mut baseline_control).unwrap();
        let Signature::View { body, .. } =
            &prepared.inputs().law().declarations["Calc.retain"].signature
        else {
            unreachable!()
        };
        let parameter_span = prepared.inputs().law().exprs[*body].span;
        assert_eq!(
            &sources.law().bytes()[parameter_span.0..parameter_span.1],
            b"x"
        );
        let normal = evaluate_observed(prepared, &mut baseline_control).unwrap();
        assert_eq!(normal.status(), "partial");
        let Json::Obj(ref normal_wire) = normal.wire() else {
            unreachable!()
        };
        let Json::Arr(normal_answers) = &normal_wire["answers"] else {
            unreachable!()
        };
        assert_eq!(normal.answers[0].status, Decision::Established);
        let graph = rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        assert_eq!(
            graph.scalar(normal.answers[0].outputs["value"]).unwrap(),
            &Scalar::Q((-2).into(), 3.into())
        );
        let parameter_evaluation = normal
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (normal.contexts[index].frame == Some(0)
                    && matches!(&node.payload, Some(Payload::Evaluation { .. })))
                .then_some(index)
            })
            .unwrap();
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..=parameter_evaluation])
            .unwrap();
        let Some(Payload::Evaluation { parts, value, .. }) =
            &normal.nodes[parameter_evaluation].payload
        else {
            unreachable!()
        };
        assert_eq!(
            parts[0].location,
            Location::Law {
                span: parameter_span
            }
        );
        assert_eq!(parts[0].children.len(), 1);
        assert!(value.is_none());
        let target_context = super::super::call::Context {
            request: 2,
            frame: Some(0),
            iteration: None,
        };
        let mut problems = Vec::new();
        for kind in 0..3 {
            let (limits, usage, expected) = match kind {
                0 => (
                    Limits {
                        time_ms: Some(1),
                        memory_mib: None,
                    },
                    Usage {
                        elapsed_ms: 1,
                        ..Usage::default()
                    },
                    StopReason::BudgetExhausted {
                        resource: Resource::TimeMs,
                        limit: 1,
                        observed: 1,
                    },
                ),
                1 => (
                    Limits {
                        time_ms: None,
                        memory_mib: Some(1),
                    },
                    Usage {
                        memory_mib: 1,
                        ..Usage::default()
                    },
                    StopReason::BudgetExhausted {
                        resource: Resource::MemoryMib,
                        limit: 1,
                        observed: 1,
                    },
                ),
                _ => (
                    Limits::default(),
                    Usage {
                        signal: Some(Signal::Term),
                        ..Usage::default()
                    },
                    StopReason::Cancelled(Signal::Term),
                ),
            };
            let armed = Rc::new(Cell::new(false));
            let probes = Rc::new(Cell::new(0));
            let frozen = Rc::new(Cell::new(None));
            let seen = Rc::new(RefCell::new(Vec::new()));
            let (probe_armed, probe_count, at_stop) =
                (armed.clone(), probes.clone(), frozen.clone());
            let mut control = Control::new(limits, move |point| {
                probe_count.set(probe_count.get() + 1);
                if probe_armed.replace(false) {
                    assert_eq!(point, Checkpoint::FiniteIteration);
                    assert!(
                        at_stop.replace(Some(probe_count.get())).is_none(),
                        "同じ既存tick一箇所だけへ注入する"
                    );
                    return usage;
                }
                Usage::default()
            });
            let prepared = prepare_observed(sources.clone(), &asks, &mut control).unwrap();
            let result = evaluate_observed_with_validator(
                prepared,
                &mut control,
                |environment, graph, request, answer| {
                    // 元のvalidatorを通した先行欠測Answerの後に、同じEnvironmentを観測する。
                    environment.validate_answer(graph, request, answer)?;
                    if request.id == "missing" {
                        assert!(
                            answer
                                .reasons
                                .iter()
                                .any(|r| matches!(r.kind, ReasonKind::Missing))
                        );
                        let (observed, arm) = (seen.clone(), armed.clone());
                        environment.observe_optional_name_token(move |span, context| {
                            if span == parameter_span && context == target_context {
                                observed.borrow_mut().push((span, context));
                                arm.set(true);
                            }
                        });
                    }
                    Ok(())
                },
            )
            .unwrap();
            assert_eq!(
                result.nodes.len(),
                parameter_evaluation,
                "停止したparameter評価をcommitせず新nodeを追加しない"
            );
            assert_eq!(&*seen.borrow(), &[(parameter_span, target_context)]);
            assert_eq!(control.stop_reason(), Some(expected.clone()));
            assert_eq!(
                Some(probes.get()),
                frozen.get(),
                "停止後はprobeを再開しない"
            );
            let Json::Obj(ref wire) = result.wire() else {
                unreachable!()
            };
            let Json::Arr(answers) = &wire["answers"] else {
                unreachable!()
            };
            assert_eq!(
                &answers[..2],
                &normal_answers[..2],
                "先行確定値と元missing/依存を保持する"
            );
            for index in [2, 3] {
                let answer = &result.answers[index];
                assert_eq!(answer.status, Decision::Undetermined);
                assert!(
                    answer.outputs.is_empty(),
                    "未完成/未着手を通常値へ昇格しない"
                );
                if !answer
                    .reasons
                    .iter()
                    .any(|r| matches!(&r.kind, ReasonKind::Stop(stop) if stop == &expected))
                {
                    problems.push(format!(
                        "{kind}:{}の元停止理由を失った: {:?}",
                        answer.id, answer.reasons
                    ));
                }
            }
            assert!(
                result.answers[2]
                    .reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::Missing)
                        && r.missing
                            .iter()
                            .any(|f| f.field.as_deref() == Some("Numeric.Sample.p"))),
                "current引数の元missingを保持する"
            );
            if result.status() != "interrupted" {
                problems.push(format!("{kind}:status={}", result.status()));
            }
            if result
                .issues
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Internal(_)))
            {
                problems.push(format!("{kind}:停止をInternalへ変えた"));
            }
            rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
            let before = probes.get();
            assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
            assert_eq!(probes.get(), before);
        }
        assert!(
            problems.is_empty(),
            "同じname_token内既存tickで3種類の停止を保持する: {problems:#?}"
        );
    }
    fn data_recheck_example(omitted: &[&str], requests: &[&str]) -> ObservedEvaluation {
        let original = numeric_recheck_fixture(
            &[],
            r#"
 view make(): Packet = Pair(1,2);
 view matched(): Z = match Packet.Pair(7,7) { Pair(left,right) => let copy=right in left+copy; Swap(_,_) => 0; Empty => 0; };
 view inner(x: Packet): Z = match x { Pair(left,right) => left; Swap(_,_) => 0; Empty => 0; };
 view caller(): Z = inner(Pair(7,7))+inner(Pair(7,7));
 view observed(s: Sample): Packet = s.packet;
 view unknown(s: Sample): Z = match s.packet { Pair(left,right) => left; Swap(_,_) => 0; Empty => 0; };
 view nested(): Z = match Envelope.Wrap(Pair(7,7)) { Wrap(Pair(left,_)) => left; _ => 0; };
"#,
        );
        let definitions = std::str::from_utf8(original.definitions()[0].bytes()).unwrap()
            .replace(r#""declarations":["#, r#""declarations":[
{"kind":"data","name":"Numeric.Packet","meaning":"数値の組を区別する。","constructors":[{"name":"Pair","arguments":["Z","Z"],"meaning":"組。"},{"name":"Swap","arguments":["Z","Z"],"meaning":"別の組。"},{"name":"Empty","arguments":[],"meaning":"空。"}]},
{"kind":"data","name":"Numeric.Envelope","meaning":"組を包む。","constructors":[{"name":"Wrap","arguments":[["Data","Numeric.Packet"]],"meaning":"包み。"}]},
{"kind":"data","name":"Numeric.Other","meaning":"異なる型の組。","constructors":[{"name":"Pair","arguments":["Z","Z"],"meaning":"組。"}]},"#)
            .replace(r#""fields":["#, r#""fields":[{"name":"packet","type":["Data","Numeric.Packet"],"meaning":"観測した組。"},"#);
        let checked = crate::definition::check_definitions_controlled(
            &[("definition0", definitions.as_bytes())],
            &mut named_call_quiet(),
        )
        .unwrap();
        let previous = crate::definition::check_definitions_controlled(
            &[("definition0", original.definitions()[0].bytes())],
            &mut named_call_quiet(),
        )
        .unwrap();
        let old_digest = &previous.vocabularies["Numeric"].digest;
        let new_digest = &checked.vocabularies["Numeric"].digest;
        let law = std::str::from_utf8(original.law().bytes())
            .unwrap()
            .replace(old_digest, new_digest);
        let mut map = std::str::from_utf8(original.archmap().bytes())
            .unwrap()
            .replace(old_digest, new_digest);
        if !omitted.contains(&"packet") {
            map = map.replace(r#""atoms":["#, r#""atoms":[{"id":"packet","subject":"sample","field":"Numeric.Sample.packet","value":{"tag":"Pair","args":["7","7"]},"origin":"values"},"#);
        }
        evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![definitions.into_bytes()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            requests,
            &mut named_call_quiet(),
        )
        .unwrap()
    }
    fn data_rule_scalar(result: &ObservedEvaluation, source: &str, request: usize) -> usize {
        result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                if result.contexts[index].request != request
                    || !matches!(node.payload, Some(Payload::Scalar(_)))
                {
                    return None;
                }
                let Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                } = &node.rule
                else {
                    return None;
                };
                (result
                    .prepared
                    .inputs()
                    .sources()
                    .law()
                    .bytes()
                    .get(span.0..span.1)
                    == Some(source.as_bytes()))
                .then_some(index)
            })
            .unwrap()
    }
    fn data_scalar_at(result: &ObservedEvaluation, index: usize) -> &Scalar {
        match &result.nodes[index].payload {
            Some(Payload::Scalar(scalar)) => scalar,
            _ => panic!("通常Scalarでない"),
        }
    }
    #[test]
    fn data_constructors_recheck_family_tag_argument_order_and_payload_type_at_prefix() {
        let result = data_recheck_example(&[], &["value=evaluate(Calc.make)"]);
        assert_eq!(result.status(), "complete");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let value = data_rule_scalar(&result, "Pair(1,2)", 0);
        let prefix = &result.nodes[..=value];
        rebuild_for_origin_and_support_recheck(&result, prefix).unwrap();
        for mutation in 0..4 {
            let mut changed = prefix.to_vec();
            let node = &mut changed[value];
            let Some(Payload::Scalar(Scalar::Data {
                family,
                constructor,
                args,
            })) = &mut node.payload
            else {
                unreachable!()
            };
            match mutation {
                0 => {
                    *family = "Numeric.Other".into();
                    *constructor = "Numeric.Other.Pair".into();
                    node.ty = NodeType::Value(Type::Data(family.clone()));
                }
                1 => *constructor = "Numeric.Packet.Swap".into(),
                2 => {
                    args.swap(0, 1);
                    node.arguments.swap(0, 1);
                }
                _ => args[0] = Scalar::Q(1.into(), 1.into()),
            }
            rejects_named_prefix(&result, &changed);
        }
        rebuild_for_origin_and_support_recheck(&result, prefix).unwrap();
    }
    #[test]
    fn data_matches_recheck_selected_arm_binder_path_scope_and_support_at_prefix() {
        let result = data_recheck_example(
            &[],
            &[
                "value=evaluate(Calc.matched)",
                "nested=evaluate(Calc.nested)",
            ],
        );
        assert_eq!(result.status(), "complete");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let binder = data_rule_scalar(&result, "left", 0);
        let prefix = &result.nodes[..=binder];
        rebuild_for_origin_and_support_recheck(&result, prefix).unwrap();
        let right = data_rule_scalar(&result, "right", 0);
        assert!(right < binder);
        assert_eq!(
            data_scalar_at(&result, binder),
            data_scalar_at(&result, right)
        );
        // 同型同値でも別のconstructor引数位置を読む元名へ付け替えない。
        let mut changed = prefix.to_vec();
        changed[binder].rule = changed[right].rule.clone();
        // rule単独をrightへ変えれば独立した正しいright読取りになるので、
        // 元leftを主張するEvaluationまでのprefixで元使用出現との対応を検査する。
        let evaluation = result.nodes.iter().enumerate().find_map(|(index, node)| {
            matches!(&node.payload, Some(Payload::Evaluation { value: Some(value), .. }) if value.0 == binder).then_some(index)
        }).unwrap();
        changed.extend_from_slice(&result.nodes[changed.len()..=evaluation]);
        rejects_named_prefix(&result, &changed);
        for mutation in 0..2 {
            let mut changed = prefix.to_vec();
            if mutation == 0 {
                changed[binder].scope.readings.insert("Foreign".into());
            } else {
                changed[binder].support.push(Fact {
                    snapshot: "v".into(),
                    subject: "sample".into(),
                    field: None,
                    atom: None,
                });
            }
            rejects_named_prefix(&result, &changed);
        }
        let root = result.answers[0].outputs["evaluation"].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=root]).unwrap();
        let mut changed = result.nodes[..=root].to_vec();
        let id = *result
            .prepared
            .inputs()
            .law()
            .declarations
            .get("Calc.matched")
            .map(|d| match &d.signature {
                Signature::View { body, .. } => body,
                _ => unreachable!(),
            })
            .unwrap();
        let ExprKind::Match { arms, .. } = &result.prepared.inputs().law().exprs[id].kind else {
            unreachable!()
        };
        let selected = match &changed[root].payload {
            Some(Payload::Evaluation { parts, .. }) => parts[0].children[1],
            _ => unreachable!(),
        };
        let source = match &changed[selected.0].payload {
            Some(Payload::Evaluation { expression, .. }) => *expression,
            _ => unreachable!(),
        };
        let wrong_span = result.prepared.inputs().law().exprs[arms[1].body].span;
        let Some(Payload::Expression { location, .. }) = &mut changed[source.0].payload else {
            unreachable!()
        };
        *location = Location::Law { span: wrong_span };
        changed[source.0].rule = Rule::Input {
            kind: "law",
            location: Location::Law { span: wrong_span },
        };
        rejects_named_prefix(&result, &changed);
    }
    #[test]
    fn data_matches_reject_equal_binder_producers_from_other_calls_and_requests() {
        let result = data_recheck_example(
            &[],
            &[
                "first=evaluate(Calc.caller)",
                "second=evaluate(Calc.caller)",
            ],
        );
        assert_eq!(result.status(), "complete");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let binders: Vec<_> = result
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                let Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                } = &node.rule
                else {
                    return None;
                };
                (matches!(node.payload, Some(Payload::Scalar(Scalar::Z(_))))
                    && result
                        .prepared
                        .inputs()
                        .sources()
                        .law()
                        .bytes()
                        .get(span.0..span.1)
                        == Some(b"left"))
                .then_some(index)
            })
            .collect();
        assert_eq!(binders.len(), 4);
        for (earlier, later) in [(binders[0], binders[1]), (binders[0], binders[2])] {
            assert_eq!(
                data_scalar_at(&result, earlier),
                data_scalar_at(&result, later)
            );
            assert_ne!(result.contexts[earlier], result.contexts[later]);
            let evaluation = result.nodes.iter().enumerate().find_map(|(index,node)| matches!(&node.payload,Some(Payload::Evaluation{value:Some(value),..}) if value.0==later).then_some(index)).unwrap();
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=evaluation]).unwrap();
            let mut changed = result.nodes[..=evaluation].to_vec();
            let Some(Payload::Evaluation { value, parts, .. }) = &mut changed[evaluation].payload
            else {
                unreachable!()
            };
            *value = Some(NodeRef(earlier));
            parts[0].value = *value;
            for argument in &mut changed[evaluation].arguments {
                if argument.0 == later {
                    *argument = NodeRef(earlier);
                }
            }
            rejects_named_prefix(&result, &changed);
        }
    }
    #[test]
    fn unknown_data_match_prefix_keeps_missing_without_tag_binder_or_free_parameter() {
        let result = data_recheck_example(
            &["packet"],
            &[
                "direct=evaluate(Calc.observed,s=@v/sample)",
                "unknown=evaluate(Calc.unknown,s=@v/sample)",
            ],
        );
        assert_eq!(result.status(), "partial");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let root = result.answers[1].outputs["evaluation"].0;
        let Some(Payload::Evaluation {
            parts,
            value,
            expression,
            ..
        }) = &result.nodes[root].payload
        else {
            unreachable!()
        };
        assert!(value.is_none());
        assert_eq!(parts[0].children.len(), 1);
        assert!(
            result
                .nodes
                .iter()
                .all(|n| !matches!(n.payload, Some(Payload::Scalar(Scalar::Data { .. }))))
        );
        assert!(result.answers[1].reasons.iter().any(|r| {
            r.missing
                .iter()
                .any(|f| f.field.as_deref() == Some("Numeric.Sample.packet") && f.atom.is_none())
        }));
        let source = expression.0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source]).unwrap();
        let mut changed = result.nodes[..=source].to_vec();
        let Some(Payload::Expression { parameters, .. }) = &mut changed[source].payload else {
            unreachable!()
        };
        parameters.push(("left".into(), Type::Z));
        rejects_named_prefix(&result, &changed);
        let mut changed = result.nodes[..=root].to_vec();
        let Some(Payload::Evaluation { parts, .. }) = &mut changed[root].payload else {
            unreachable!()
        };
        let child = parts[0].children[0];
        parts[0].children.push(child);
        changed[root].arguments.insert(2, child);
        rejects_named_prefix(&result, &changed);
    }
    fn container_recheck_example(omitted: &[&str], requests: &[&str]) -> ObservedEvaluation {
        evaluate_observed_bytes(numeric_recheck_fixture(omitted, r#"
 view ordered(): List<Z> = list<Z>[2,1,2];
 view unique(): Set<Z> = set<Z>{2,1,2};
 view mixed(): (Unit,Text,Bool,List<Z>) = (unit,"kept",false,list<Z>[2,1,2]);
 view absent(): Option<Z> = none<Z>;
 view present(): Option<Z> = some(2);
 view echo(x: List<Z>): List<Z> = x;
 view called(): (List<Z>,List<Z>) = (echo(list<Z>[2,1]),echo(list<Z>[2,1]));
 view unknown(s: Sample): List<Q> = list<Q>[s.q];
 view maybe(s: Sample): Option<Q> = some(s.q);
 view total(s: Sample): Q = sum(list<Q>[s.q]);
 view empty(): (Z,Q,Fp(5),(Z,Q,Fp(5))) = (sum(list<Z>[]),sum(set<Q>{}),sum(list<Fp(5)>[]),sum(list<(Z,Q,Fp(5))>[]));
"#),requests,&mut named_call_quiet()).unwrap()
    }
    #[test]
    fn primitive_containers_recheck_sequence_type_and_option_tags_at_scalar_prefix() {
        let result = container_recheck_example(
            &[],
            &[
                "ordered=evaluate(Calc.ordered)",
                "mixed=evaluate(Calc.mixed)",
                "absent=evaluate(Calc.absent)",
            ],
        );
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let list = data_rule_scalar(&result, "list<Z>[2,1,2]", 0);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=list]).unwrap();
        let mut changed = result.nodes[..=list].to_vec();
        let Some(Payload::Scalar(Scalar::List { items, .. })) = &mut changed[list].payload else {
            unreachable!()
        };
        items.swap(0, 1);
        changed[list].arguments.swap(0, 1);
        rejects_named_prefix(&result, &changed);
        let mut changed = result.nodes[..=list].to_vec();
        let Some(Payload::Scalar(Scalar::List { element, .. })) = &mut changed[list].payload else {
            unreachable!()
        };
        *element = Type::Q;
        changed[list].ty = NodeType::Value(Type::List(Box::new(Type::Q)));
        rejects_named_prefix(&result, &changed);
        let mixed = result.answers[1].outputs["value"].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=mixed]).unwrap();
        let mut changed = result.nodes[..=mixed].to_vec();
        let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut changed[mixed].payload else {
            unreachable!()
        };
        items.swap(0, 1);
        let ty = Type::Tuple(items.iter().map(Scalar::ty).collect());
        changed[mixed].ty = NodeType::Value(ty);
        changed[mixed].arguments.swap(0, 1);
        rejects_named_prefix(&result, &changed);
        let absent = result.answers[2].outputs["value"].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=absent]).unwrap();
        let mut changed = result.nodes[..=absent].to_vec();
        let Some(Payload::Scalar(Scalar::Option { value, .. })) = &mut changed[absent].payload
        else {
            unreachable!()
        };
        *value = Some(Box::new(Scalar::Z(0.into())));
        rejects_named_prefix(&result, &changed);
    }
    #[test]
    fn primitive_sets_keep_all_source_children_and_accept_extensional_display_order() {
        let result = container_recheck_example(&[], &["value=evaluate(Calc.unique)"]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let value = result.answers[0].outputs["value"].0;
        let root = result.answers[0].outputs["evaluation"].0;
        let Scalar::Set { items, .. } = data_scalar_at(&result, value) else {
            unreachable!()
        };
        assert_eq!(items, &vec![Scalar::Z(2.into()), Scalar::Z(1.into())]);
        let Some(Payload::Evaluation { parts, .. }) = &result.nodes[root].payload else {
            unreachable!()
        };
        assert_eq!(parts[0].children.len(), 3);
        assert_eq!(result.nodes[value].arguments.len(), 3);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=value]).unwrap();
        let mut display = result.nodes.clone();
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut display[value].payload else {
            unreachable!()
        };
        items.reverse();
        // 同じ集合の独立な表示順は、数学的に不正な導出へ数えない。
        rebuild_for_origin_and_support_recheck(&result, &display[..=value]).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &display).unwrap();
        let mut duplicate = result.nodes[..=value].to_vec();
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut duplicate[value].payload else {
            unreachable!()
        };
        items.push(items[0].clone());
        rejects_named_prefix(&result, &duplicate);
        let mut omitted = result.nodes[..=value].to_vec();
        omitted[value].arguments.pop();
        rejects_named_prefix(&result, &omitted);
        let mut reordered = result.nodes[..=value].to_vec();
        reordered[value].arguments.swap(0, 1);
        rejects_named_prefix(&result, &reordered);
    }
    #[test]
    fn primitive_container_sources_reject_other_call_producers_scope_and_support() {
        let result = container_recheck_example(
            &[],
            &[
                "first=evaluate(Calc.called)",
                "second=evaluate(Calc.called)",
            ],
        );
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let values:Vec<_>=result.nodes.iter().enumerate().filter_map(|(index,node)| {
            (result.contexts[index].frame.is_none() && matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span}} if result.prepared.inputs().sources().law().bytes().get(span.0..span.1)==Some(b"echo(list<Z>[2,1])")) && matches!(node.payload,Some(Payload::Scalar(_)))).then_some(index)
        }).collect();
        assert_eq!(values.len(), 4);
        for (early, later) in [(values[0], values[1]), (values[0], values[2])] {
            assert_eq!(
                data_scalar_at(&result, early),
                data_scalar_at(&result, later)
            );
            let evaluation=result.nodes.iter().enumerate().find_map(|(index,node)| matches!(&node.payload,Some(Payload::Evaluation {value:Some(value),..}) if value.0==later).then_some(index)).unwrap();
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=evaluation]).unwrap();
            let mut changed = result.nodes[..=evaluation].to_vec();
            let Some(Payload::Evaluation { value, parts, .. }) = &mut changed[evaluation].payload
            else {
                unreachable!()
            };
            *value = Some(NodeRef(early));
            parts[0].value = *value;
            for argument in &mut changed[evaluation].arguments {
                if argument.0 == later {
                    *argument = NodeRef(early);
                }
            }
            rejects_named_prefix(&result, &changed);
        }
        let later = values[1];
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=later]).unwrap();
        for mutation in 0..3 {
            let mut changed = result.nodes[..=later].to_vec();
            match mutation {
                0 => changed[later].scope.readings.insert("Foreign".into()),
                1 => {
                    changed[later].support.push(Fact {
                        snapshot: "v".into(),
                        subject: "sample".into(),
                        field: None,
                        atom: None,
                    });
                    true
                }
                _ => {
                    changed[later].rule = changed[values[0]].rule.clone();
                    true
                }
            };
            rejects_named_prefix(&result, &changed);
        }
    }
    #[test]
    fn primitive_empty_sums_keep_exact_types_and_missing_elements_stay_blocked() {
        let known = container_recheck_example(
            &[],
            &[
                "empty=evaluate(Calc.empty)",
                "absentvalue=evaluate(Calc.absent)",
                "presentvalue=evaluate(Calc.present)",
            ],
        );
        assert_eq!(known.status(), "complete", "{:?}", known.issues);
        rebuild_for_origin_and_support_recheck(&known, &known.nodes).unwrap();
        let zero = Scalar::Tuple(vec![
            Scalar::Z(0.into()),
            Scalar::Q(0.into(), 1.into()),
            Scalar::Fp {
                modulus: "5".into(),
                value: 0.into(),
            },
            Scalar::Tuple(vec![
                Scalar::Z(0.into()),
                Scalar::Q(0.into(), 1.into()),
                Scalar::Fp {
                    modulus: "5".into(),
                    value: 0.into(),
                },
            ]),
        ]);
        assert_eq!(
            data_scalar_at(&known, known.answers[0].outputs["value"].0),
            &zero
        );
        let missing = container_recheck_example(
            &["q"],
            &[
                "unknownlist=evaluate(Calc.unknown,s=@v/sample)",
                "unknownoption=evaluate(Calc.maybe,s=@v/sample)",
                "unknowntotal=evaluate(Calc.total,s=@v/sample)",
            ],
        );
        assert_eq!(missing.status(), "partial", "{:?}", missing.issues);
        rebuild_for_origin_and_support_recheck(&missing, &missing.nodes).unwrap();
        for answer in &missing.answers {
            assert!(!answer.outputs.contains_key("value"));
            assert!(answer.reasons.iter().any(|r| {
                r.missing
                    .iter()
                    .any(|f| f.field.as_deref() == Some("Numeric.Sample.q"))
            }));
        }
        let root = missing.answers[1].outputs["evaluation"].0;
        rebuild_for_origin_and_support_recheck(&missing, &missing.nodes[..=root]).unwrap();
        let mut forged = missing.nodes[..=root].to_vec();
        let Some(Payload::Evaluation { parts, .. }) = &mut forged[root].payload else {
            unreachable!()
        };
        parts[0].children.clear();
        forged[root].arguments.remove(1);
        rejects_named_prefix(&missing, &forged);
    }

    #[test]
    fn primitive_set_and_sum_iterations_preserve_original_stop_inside_actual_evaluation() {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{
            cell::{Cell, RefCell},
            rc::Rc,
        };
        for operation in ["set", "sum"] {
            let (returns, body) = if operation == "set" {
                ("Set<Z>", "set<Z>{1,2,1}")
            } else {
                ("Z", "sum(list<Z>[1,2,3])")
            };
            let sources = numeric_recheck_fixture(
                &["p"],
                &format!(
                    r#"
 view seed(s: Sample): Q = s.q;
 view missing(s: Sample): Bool = s.p;
 view current(s: Sample): {returns} = {body};
 view later(s: Sample): Q = s.q;
"#
                ),
            );
            let asks = [
                "seed=evaluate(Calc.seed,s=@v/sample)",
                "missing=evaluate(Calc.missing,s=@v/sample)",
                "current=evaluate(Calc.current,s=@v/sample)",
                "later=evaluate(Calc.later,s=@v/sample)",
            ];
            let mut control = named_call_quiet();
            let prepared = prepare_observed(sources.clone(), &asks, &mut control).unwrap();
            let Signature::View {
                body: expression, ..
            } = &prepared.inputs().law().declarations["Calc.current"].signature
            else {
                unreachable!()
            };
            let target = prepared.inputs().law().exprs[*expression].span;
            assert_eq!(&sources.law().bytes()[target.0..target.1], body.as_bytes());
            let context = super::super::call::Context {
                request: 2,
                frame: None,
                iteration: None,
            };
            let seen = Rc::new(RefCell::new(Vec::new()));
            let progress = seen.clone();
            data::observe_iterations(move |span, actual, name, index| {
                if span == target && actual == context && name == operation {
                    progress.borrow_mut().push(index);
                }
            });
            let normal = evaluate_observed(prepared, &mut control);
            data::clear_iteration_observer();
            let normal = normal.unwrap();
            assert_eq!(normal.status(), "partial", "{:?}", normal.issues);
            assert_eq!(
                &*seen.borrow(),
                &[0, 1, 2],
                "Source再解析を混ぜず実評価の三要素の進行だけを観測する"
            );
            let graph = rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
            let value = normal.answers[2].outputs["value"];
            if operation == "sum" {
                assert_eq!(graph.scalar(value).unwrap(), &Scalar::Z(6.into()));
            } else {
                assert_eq!(
                    graph.scalar(value).unwrap(),
                    &Scalar::Set {
                        element: Type::Z,
                        items: vec![Scalar::Z(1.into()), Scalar::Z(2.into())]
                    }
                );
            }
            let scalar = value.0;
            rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..scalar]).unwrap();
            let Json::Obj(ref normal_wire) = normal.wire() else {
                unreachable!()
            };
            let Json::Arr(normal_answers) = &normal_wire["answers"] else {
                unreachable!()
            };
            for kind in 0..3 {
                let (limits, usage, expected) = match kind {
                    0 => (
                        Limits {
                            time_ms: Some(1),
                            memory_mib: None,
                        },
                        Usage {
                            elapsed_ms: 1,
                            ..Usage::default()
                        },
                        StopReason::BudgetExhausted {
                            resource: Resource::TimeMs,
                            limit: 1,
                            observed: 1,
                        },
                    ),
                    1 => (
                        Limits {
                            time_ms: None,
                            memory_mib: Some(1),
                        },
                        Usage {
                            memory_mib: 1,
                            ..Usage::default()
                        },
                        StopReason::BudgetExhausted {
                            resource: Resource::MemoryMib,
                            limit: 1,
                            observed: 1,
                        },
                    ),
                    _ => (
                        Limits::default(),
                        Usage {
                            signal: Some(Signal::Term),
                            ..Usage::default()
                        },
                        StopReason::Cancelled(Signal::Term),
                    ),
                };
                let armed = Rc::new(Cell::new(false));
                let probes = Rc::new(Cell::new(0));
                let frozen = Rc::new(Cell::new(None));
                let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
                let mut control = Control::new(limits, move |point| {
                    count.set(count.get() + 1);
                    if arm.replace(false) {
                        assert_eq!(point, Checkpoint::FiniteIteration);
                        assert!(freeze.replace(Some(count.get())).is_none());
                        usage
                    } else {
                        Usage::default()
                    }
                });
                let prepared = prepare_observed(sources.clone(), &asks, &mut control).unwrap();
                let seen = Rc::new(RefCell::new(Vec::new()));
                let observed = seen.clone();
                let result = evaluate_observed_with_validator(
                    prepared,
                    &mut control,
                    |environment, graph, request, answer| {
                        environment.validate_answer(graph, request, answer)?;
                        if request.id == "missing" {
                            let (observed, armed) = (observed.clone(), armed.clone());
                            data::observe_iterations(move |span, actual, name, index| {
                                if span == target && actual == context && name == operation {
                                    observed.borrow_mut().push(index);
                                    if index == 1 {
                                        armed.set(true);
                                    }
                                }
                            });
                        }
                        Ok(())
                    },
                );
                data::clear_iteration_observer();
                let result = result.unwrap();
                assert_eq!(
                    &*seen.borrow(),
                    &[0, 1],
                    "実評価loopの第一要素完了後、第二要素の既存tickで停止する"
                );
                assert_eq!(
                    result.nodes.len(),
                    scalar,
                    "未完成のcontainer/sum値をcommitしない"
                );
                assert_eq!(control.stop_reason(), Some(expected.clone()));
                assert_eq!(Some(probes.get()), frozen.get());
                assert_eq!(result.status(), "interrupted", "{:?}", result.issues);
                assert!(
                    result
                        .issues
                        .iter()
                        .all(|r| !matches!(r.kind, ReasonKind::Internal(_)))
                );
                let Json::Obj(ref wire) = result.wire() else {
                    unreachable!()
                };
                let Json::Arr(answers) = &wire["answers"] else {
                    unreachable!()
                };
                assert_eq!(
                    &answers[..2],
                    &normal_answers[..2],
                    "先行値と元missingを保持する"
                );
                for answer in &result.answers[2..] {
                    assert_eq!(answer.status, Decision::Undetermined);
                    assert!(answer.outputs.is_empty());
                    assert!(
                        answer.reasons.iter().any(
                            |r| matches!(&r.kind,ReasonKind::Stop(actual) if actual==&expected)
                        )
                    );
                }
                rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
                let before = probes.get();
                assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
                assert_eq!(probes.get(), before);
            }
        }
    }
    fn comprehension_recheck_example(requests: &[&str]) -> ObservedEvaluation {
        evaluate_observed_bytes(
            numeric_recheck_fixture(
                &[],
                r#"
 view list_case(): Set<Z> = let older=list<Z>[2,1,2] in set { x+1 | x in list<Z>[2,1,2] where x>1 };
 view set_case(): Set<Z> = set { x+1 | x in set<Z>{2,1} };
 view repeated(): (Set<Z>,Set<Z>) = (list_case(),list_case());
"#,
            ),
            requests,
            &mut named_call_quiet(),
        )
        .unwrap()
    }
    fn iteration_binder_scalar(result: &ObservedEvaluation, iteration: usize) -> usize {
        result.nodes.iter().enumerate().find_map(|(index,node)| {
            (result.contexts[index].iteration==Some(iteration) && matches!(&node.payload,Some(Payload::Scalar(_))) && matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span}} if result.prepared.inputs().sources().law().bytes().get(span.0..span.1)==Some(b"x"))).then_some(index)
        }).unwrap()
    }
    fn replace_comprehension_children(
        nodes: &mut [Node],
        evaluation: usize,
        children: Vec<NodeRef>,
    ) {
        let (expression, value) = match &mut nodes[evaluation].payload {
            Some(Payload::Evaluation {
                expression,
                value,
                parts,
                ..
            }) => {
                parts[0].children = children.clone();
                (*expression, *value)
            }
            _ => unreachable!(),
        };
        nodes[evaluation].arguments = std::iter::once(expression)
            .chain(children.iter().copied())
            .chain(value)
            .collect();
        if let Some(value) = value {
            nodes[value.0].arguments = children;
        }
    }
    #[test]
    fn set_comprehension_prefix_rechecks_domain_list_position_binder_type_and_value() {
        let mut result = comprehension_recheck_example(&["value=evaluate(Calc.list_case)"]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let binder = iteration_binder_scalar(&result, 0);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=binder]).unwrap();
        let original = result.iterations[0].clone();
        result.iterations[0].member = super::super::call::Member::ListPosition(1);
        rejects_named_prefix(&result, &result.nodes[..=binder]);
        result.iterations[0] = original.clone();
        for mutation in 0..2 {
            let mut changed = result.nodes[..=binder].to_vec();
            if mutation == 0 {
                changed[binder].payload = Some(Payload::Scalar(Scalar::Z(1.into())));
            } else {
                changed[binder].payload = Some(Payload::Scalar(Scalar::Q(2.into(), 1.into())));
                changed[binder].ty = NodeType::Value(Type::Q);
            }
            rejects_named_prefix(&result, &changed);
        }
        let earlier=result.nodes.iter().enumerate().find_map(|(index,node)| {
            (index<original.domain.0 && matches!(&node.payload,Some(Payload::Evaluation {value:Some(value),..}) if matches!(&result.nodes[value.0].payload,Some(Payload::Scalar(Scalar::List {..}))))).then_some(NodeRef(index))
        }).unwrap();
        assert_ne!(earlier, original.domain);
        assert_eq!(
            data_scalar_at(
                &result,
                match &result.nodes[earlier.0].payload {
                    Some(Payload::Evaluation {
                        value: Some(value), ..
                    }) => value.0,
                    _ => unreachable!(),
                }
            ),
            data_scalar_at(
                &result,
                match &result.nodes[original.domain.0].payload {
                    Some(Payload::Evaluation {
                        value: Some(value), ..
                    }) => value.0,
                    _ => unreachable!(),
                }
            )
        );
        result.iterations[0].domain = earlier;
        let mut changed = result.nodes[..=binder].to_vec();
        for (index, node) in changed.iter_mut().enumerate() {
            if result.contexts[index].iteration == Some(0) {
                for reference in &mut node.arguments {
                    if *reference == original.domain {
                        *reference = earlier;
                    }
                }
            }
        }
        rejects_named_prefix(&result, &changed);
        result.iterations[0] = original;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
    #[test]
    fn set_comprehension_completed_walk_rejects_omitted_duplicate_or_misclassified_children() {
        let mut result = comprehension_recheck_example(&["value=evaluate(Calc.list_case)"]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let root = result.answers[0].outputs["evaluation"].0;
        let comp = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.payload {
                Some(Payload::Evaluation { expression, .. }) => {
                    match &result.nodes[expression.0].payload {
                        Some(Payload::Expression {
                            location: Location::Law { span },
                            ..
                        }) if result
                            .prepared
                            .inputs()
                            .sources()
                            .law()
                            .bytes()
                            .get(span.0..span.1)
                            .is_some_and(|text| text.starts_with(b"set {")) =>
                        {
                            Some(index)
                        }
                        _ => None,
                    }
                }
                _ => None,
            })
            .unwrap();
        assert!(comp < root);
        let Some(Payload::Evaluation {
            parts,
            value: Some(value),
            ..
        }) = &result.nodes[comp].payload
        else {
            unreachable!()
        };
        let scalar = value.0;
        let children = parts[0].children.clone();
        assert_eq!(children.len(), 6);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
        // 同値位置2を読む孤立prefixは正しい読取りだが、全走査のposition0を落としてはならない。
        let original = result.iterations[0].member.clone();
        result.iterations[0].member = super::super::call::Member::ListPosition(2);
        let binder = iteration_binder_scalar(&result, 0);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=binder]).unwrap();
        rejects_named_prefix(&result, &result.nodes[..=comp]);
        result.iterations[0].member = original;
        for mutation in 0..3 {
            let mut changed = result.nodes[..=comp].to_vec();
            let mut altered = children.clone();
            match mutation {
                0 => {
                    altered.remove(2);
                }
                1 => {
                    altered.push(children[2]);
                }
                _ => {
                    altered.swap(1, 3);
                }
            }
            replace_comprehension_children(&mut changed, comp, altered);
            rejects_named_prefix(&result, &changed[..=scalar]);
        }
        let false_filter = children[3];
        let Some(Payload::Evaluation {
            value: Some(filter),
            ..
        }) = &result.nodes[false_filter.0].payload
        else {
            unreachable!()
        };
        let mut changed = result.nodes[..=filter.0].to_vec();
        let Some(Payload::Scalar(Scalar::Bool(value))) = &mut changed[filter.0].payload else {
            unreachable!()
        };
        assert!(!*value);
        *value = true;
        rejects_named_prefix(&result, &changed);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
    #[test]
    fn set_comprehension_set_members_are_extensional_and_prefix_support_is_original() {
        let mut result = comprehension_recheck_example(&["value=evaluate(Calc.set_case)"]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let domain = result.iterations[0].domain;
        let domain_value = match &result.nodes[domain.0].payload {
            Some(Payload::Evaluation {
                value: Some(value), ..
            }) => *value,
            _ => unreachable!(),
        };
        let mut display = result.nodes.clone();
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut display[domain_value.0].payload
        else {
            unreachable!()
        };
        items.reverse();
        let output = result.answers[0].outputs["value"].0;
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut display[output].payload else {
            unreachable!()
        };
        items.reverse();
        rebuild_for_origin_and_support_recheck(&result, &display[..=output]).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &display).unwrap();
        let binder = iteration_binder_scalar(&result, 0);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=binder]).unwrap();
        let original = result.iterations[0].member.clone();
        result.iterations[0].member = super::super::call::Member::SetElement(Scalar::Z(9.into()));
        rejects_named_prefix(&result, &result.nodes[..=binder]);
        result.iterations[0].member = original;
        for mutation in 0..3 {
            let mut changed = result.nodes[..=binder].to_vec();
            let source=match &changed[binder].rule {Rule::Input {location:Location::Law {span},..}=>result.nodes.iter().enumerate().find_map(|(index,node)| (index<binder&&result.contexts[index].iteration==Some(0)&&matches!(&node.payload,Some(Payload::Expression {location:Location::Law {span:actual},..}) if actual==span)).then_some(index)).unwrap(),_=>unreachable!()};
            match mutation {
                0 => {
                    changed[source].scope.readings.insert("Foreign".into());
                }
                1 => {
                    changed[binder].support.push(Fact {
                        snapshot: "v".into(),
                        subject: "sample".into(),
                        field: None,
                        atom: None,
                    });
                }
                _ => {
                    changed[source].arguments.pop();
                }
            }
            rejects_named_prefix(&result, &changed);
        }
    }
    #[test]
    fn set_comprehension_equal_binder_values_do_not_replace_other_iteration_call_or_request() {
        let result = comprehension_recheck_example(&[
            "first=evaluate(Calc.repeated)",
            "second=evaluate(Calc.repeated)",
        ]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let earlier = iteration_binder_scalar(&result, 0);
        for iteration in [2, 3, 6] {
            let later = iteration_binder_scalar(&result, iteration);
            assert_eq!(
                data_scalar_at(&result, earlier),
                data_scalar_at(&result, later)
            );
            assert_ne!(result.contexts[earlier], result.contexts[later]);
            let evaluation=result.nodes.iter().enumerate().find_map(|(index,node)|matches!(&node.payload,Some(Payload::Evaluation {value:Some(value),..}) if value.0==later).then_some(index)).unwrap();
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=evaluation]).unwrap();
            let mut changed = result.nodes[..=evaluation].to_vec();
            let Some(Payload::Evaluation { value, parts, .. }) = &mut changed[evaluation].payload
            else {
                unreachable!()
            };
            *value = Some(NodeRef(earlier));
            parts[0].value = *value;
            for argument in &mut changed[evaluation].arguments {
                if argument.0 == later {
                    *argument = NodeRef(earlier);
                }
            }
            rejects_named_prefix(&result, &changed);
        }
    }
    #[test]
    fn set_comprehension_actual_iteration_filter_and_set_loops_keep_original_stops() {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{
            cell::{Cell, RefCell},
            rc::Rc,
        };
        let sources = numeric_recheck_fixture(
            &["p"],
            r#"
 view domain(p: Bool): List<Z> = list<Z>[2,1];
 view seed(s: Sample): Q = s.q;
 view missing(s: Sample): Bool = s.p;
 view current(s: Sample): Set<Z> = set { x+1 | x in domain(s.p) where x>0 };
 view later(s: Sample): Q = s.q;
"#,
        );
        let asks = [
            "seed=evaluate(Calc.seed,s=@v/sample)",
            "missing=evaluate(Calc.missing,s=@v/sample)",
            "current=evaluate(Calc.current,s=@v/sample)",
            "later=evaluate(Calc.later,s=@v/sample)",
        ];
        let mut control = named_call_quiet();
        let prepared = prepare_observed(sources.clone(), &asks, &mut control).unwrap();
        let Signature::View { body, .. } =
            &prepared.inputs().law().declarations["Calc.current"].signature
        else {
            unreachable!()
        };
        let target = prepared.inputs().law().exprs[*body].span;
        let ExprKind::SetComp {
            filter: Some(filter),
            ..
        } = prepared.inputs().law().exprs[*body].kind
        else {
            unreachable!()
        };
        let ExprKind::Binary { rhs, .. } = prepared.inputs().law().exprs[filter].kind else {
            unreachable!()
        };
        let filter_literal = prepared.inputs().law().exprs[rhs].span;
        assert_eq!(
            &sources.law().bytes()[filter_literal.0..filter_literal.1],
            b"0"
        );
        let parent = super::super::call::Context {
            request: 2,
            frame: None,
            iteration: None,
        };
        let event = move |span, context: super::super::call::Context, name: &str, index| {
            if span == target && context == parent && name == "comprehension_iteration" {
                Some(("iteration", index))
            } else if span == filter_literal
                && context
                    == (super::super::call::Context {
                        iteration: Some(0),
                        ..parent
                    })
                && name == "expression"
            {
                Some(("filter", 0))
            } else if span == target && context == parent && name == "set" {
                Some(("set", index))
            } else {
                None
            }
        };
        let seen = Rc::new(RefCell::new(Vec::new()));
        let progress = seen.clone();
        data::observe_iterations(move |span, context, name, index| {
            if let Some(event) = event(span, context, name, index) {
                progress.borrow_mut().push(event);
            }
        });
        let normal = evaluate_observed(prepared, &mut control);
        data::clear_iteration_observer();
        let normal = normal.unwrap();
        assert_eq!(normal.status(), "partial", "{:?}", normal.issues);
        let expected_progress = [
            ("iteration", 0),
            ("filter", 0),
            ("iteration", 1),
            ("set", 0),
            ("set", 1),
        ];
        assert_eq!(
            &*seen.borrow(),
            &expected_progress,
            "実反復/実filter/結果Setだけを観測しSource再分析を含めない"
        );
        let graph = rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        assert_eq!(
            graph.scalar(normal.answers[2].outputs["value"]).unwrap(),
            &Scalar::Set {
                element: Type::Z,
                items: vec![Scalar::Z(3.into()), Scalar::Z(2.into())]
            }
        );
        let first_domain = normal.iterations[0].domain.0;
        let filter_scalar = data_rule_scalar(&normal, "0", 2);
        let result_scalar = normal.answers[2].outputs["value"].0;
        let cuts = [first_domain + 1, filter_scalar, result_scalar];
        for cut in cuts {
            rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..cut]).unwrap();
        }
        let Json::Obj(ref normal_wire) = normal.wire() else {
            unreachable!()
        };
        let Json::Arr(normal_answers) = &normal_wire["answers"] else {
            unreachable!()
        };
        for phase in 0..3 {
            let (limits, usage, expected) = match phase {
                0 => (
                    Limits::default(),
                    Usage {
                        signal: Some(Signal::Term),
                        ..Usage::default()
                    },
                    StopReason::Cancelled(Signal::Term),
                ),
                1 => (
                    Limits {
                        time_ms: Some(1),
                        memory_mib: None,
                    },
                    Usage {
                        elapsed_ms: 1,
                        ..Usage::default()
                    },
                    StopReason::BudgetExhausted {
                        resource: Resource::TimeMs,
                        limit: 1,
                        observed: 1,
                    },
                ),
                _ => (
                    Limits {
                        time_ms: None,
                        memory_mib: Some(1),
                    },
                    Usage {
                        memory_mib: 1,
                        ..Usage::default()
                    },
                    StopReason::BudgetExhausted {
                        resource: Resource::MemoryMib,
                        limit: 1,
                        observed: 1,
                    },
                ),
            };
            let armed = Rc::new(Cell::new(false));
            let probes = Rc::new(Cell::new(0));
            let frozen = Rc::new(Cell::new(None));
            let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
            let mut control = Control::new(limits, move |point| {
                count.set(count.get() + 1);
                if arm.replace(false) {
                    assert_eq!(point, Checkpoint::FiniteIteration);
                    assert!(freeze.replace(Some(count.get())).is_none());
                    usage
                } else {
                    Usage::default()
                }
            });
            let prepared = prepare_observed(sources.clone(), &asks, &mut control).unwrap();
            let seen = Rc::new(RefCell::new(Vec::new()));
            let observed = seen.clone();
            let result = evaluate_observed_with_validator(
                prepared,
                &mut control,
                |environment, graph, request, answer| {
                    environment.validate_answer(graph, request, answer)?;
                    if request.id == "missing" {
                        let (seen, armed) = (observed.clone(), armed.clone());
                        data::observe_iterations(move |span, context, name, index| {
                            if let Some(actual) = event(span, context, name, index) {
                                seen.borrow_mut().push(actual);
                                if actual == [("iteration", 0), ("filter", 0), ("set", 1)][phase] {
                                    armed.set(true);
                                }
                            }
                        });
                    }
                    Ok(())
                },
            );
            data::clear_iteration_observer();
            let result = result.unwrap();
            assert_eq!(
                &*seen.borrow(),
                &expected_progress[..[1, 2, 5][phase]],
                "元AST/親Context/反復位置/実評価phaseを確認する"
            );
            assert_eq!(
                result.nodes.len(),
                cuts[phase],
                "未完成親/結果Scalarをcommitしない"
            );
            assert_eq!(control.stop_reason(), Some(expected.clone()));
            assert_eq!(Some(probes.get()), frozen.get());
            assert_eq!(result.status(), "interrupted", "{:?}", result.issues);
            assert!(
                result
                    .issues
                    .iter()
                    .all(|r| !matches!(r.kind, ReasonKind::Internal(_)))
            );
            let Json::Obj(ref wire) = result.wire() else {
                unreachable!()
            };
            let Json::Arr(answers) = &wire["answers"] else {
                unreachable!()
            };
            assert_eq!(&answers[..2], &normal_answers[..2]);
            for answer in &result.answers[2..] {
                assert_eq!(answer.status, Decision::Undetermined);
                assert!(answer.outputs.is_empty());
                assert!(
                    answer
                        .reasons
                        .iter()
                        .any(|r| matches!(&r.kind,ReasonKind::Stop(actual) if actual==&expected))
                );
            }
            assert!(
                result.answers[2].reasons.iter().any(|r| r
                    .missing
                    .iter()
                    .any(|f| f.field.as_deref() == Some("Numeric.Sample.p"))),
                "current domain実引数の元missingを保持する"
            );
            rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
            let before = probes.get();
            assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
            assert_eq!(probes.get(), before);
        }
    }
    #[test]
    fn set_comprehension_empty_domain_does_not_implement_map_container_results() {
        let body = "set { list<Map<Sample,Sample>>[] | x in list<Z>[] }";
        let sources = numeric_recheck_fixture(
            &[],
            &format!(
                "view normal(): Set<Z> = set {{ x+1 | x in list<Z>[1] }}; view deferred(): Set<List<Map<Sample,Sample>>> = {body};"
            ),
        );
        let normal = evaluate_observed_bytes(
            sources.clone(),
            &["value=evaluate(Calc.normal)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(normal.status(), "complete");
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        let failure = evaluate_observed_bytes(
            sources.clone(),
            &["value=evaluate(Calc.deferred)"],
            &mut named_call_quiet(),
        )
        .unwrap_err();
        assert!(failure.wire().is_none());
        let EvaluationFailure::NotImplemented {
            location: Location::Law { span },
            ..
        } = failure
        else {
            panic!("Mapを含む内包結果は専用未実装を保持する")
        };
        assert_eq!(&sources.law().bytes()[span.0..span.1], body.as_bytes());
    }
    #[test]
    fn set_comprehension_captures_enclosing_let_rhs_without_reassigning_its_origin() {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(
                &[],
                "view capture(): Set<Z> = let y=10 in set { x+y | x in list<Z>[1,2] };",
            ),
            &["value=evaluate(Calc.capture)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        let value = result.answers[0].outputs["value"];
        assert_eq!(
            data_scalar_at(&result, value.0),
            &Scalar::Set {
                element: Type::Z,
                items: vec![Scalar::Z(11.into()), Scalar::Z(12.into())]
            }
        );
        assert_eq!(
            result.nodes[value.0].ty,
            NodeType::Value(Type::Set(Box::new(Type::Z)))
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let rhs = data_rule_scalar(&result, "10", 0);
        assert_eq!(result.contexts[rhs].iteration, None);
        let rhs_evaluation = result.nodes.iter().enumerate().find_map(|(index, node)| matches!(&node.payload, Some(Payload::Evaluation { value: Some(value), .. }) if value.0 == rhs).then_some(NodeRef(index))).unwrap();
        assert_eq!(result.contexts[rhs_evaluation.0].iteration, None);
        let bytes = result.prepared.inputs().sources().law().bytes();
        let mut captured = false;
        let mut scalar_prefix = false;
        for (index, node) in result.nodes.iter().enumerate() {
            if let Some(Payload::Evaluation {
                expression, parts, ..
            }) = &node.payload
                && let Some(Payload::Expression {
                    location: Location::Law { span },
                    ..
                }) = &result.nodes[expression.0].payload
                && bytes.get(span.0..span.1) == Some(b"y")
            {
                captured = true;
                assert!(result.contexts[index].iteration.is_some());
                assert_eq!(
                    parts[0].children,
                    vec![rhs_evaluation],
                    "外側letの元RHS Evaluationを参照し、反復内へ再所属させない"
                );
            }
            if matches!(&node.payload, Some(Payload::Scalar(_)))
                && matches!(&node.rule, Rule::Input { kind: "law", location: Location::Law { span } } if bytes.get(span.0..span.1) == Some(b"x+y"))
            {
                rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=index]).unwrap();
                scalar_prefix = true;
            }
        }
        assert!(captured && scalar_prefix);
    }
    #[test]
    fn set_comprehension_nested_let_and_outer_pattern_captures_keep_original_producers() {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(
                &["p"],
                r#"
 view nested_capture(): Set<Set<Z>> = set { let y=x+10 in set { y+z | z in list<Z>[1,2] } | x in list<Z>[1,2] };
 view pattern_capture(s: Sample): Set<Z> = match 10 { held => set { held+x | x in if s.p then list<Z>[1,2] else list<Z>[1,2] }; };
"#,
            ),
            &[
                "nested=evaluate(Calc.nested_capture)",
                "pattern=evaluate(Calc.pattern_capture,s=@v/sample)",
            ],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        let set = |items: &[i32]| Scalar::Set {
            element: Type::Z,
            items: items.iter().map(|n| Scalar::Z((*n).into())).collect(),
        };
        assert_eq!(
            data_scalar_at(&result, result.answers[0].outputs["value"].0),
            &Scalar::Set {
                element: Type::Set(Box::new(Type::Z)),
                items: vec![set(&[12, 13]), set(&[13, 14])],
            }
        );
        assert_eq!(
            data_scalar_at(&result, result.answers[1].outputs["value"].0),
            &set(&[11, 12])
        );
        assert!(result.answers[1].scope.completions);
        assert!(result.answers[1].reasons.iter().any(|reason| {
            reason
                .missing
                .iter()
                .any(|fact| fact.field.as_deref() == Some("Numeric.Sample.p"))
        }));
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let bytes = result.prepared.inputs().sources().law().bytes();
        let mut nested = 0;
        let mut pattern = 0;
        for (index, node) in result.nodes.iter().enumerate() {
            if let Some(Payload::Evaluation {
                expression,
                parts,
                value,
                ..
            }) = &node.payload
                && let Some(Payload::Expression {
                    location: Location::Law { span },
                    ..
                }) = &result.nodes[expression.0].payload
                && matches!(bytes.get(span.0..span.1), Some(b"y" | b"held"))
            {
                let input = parts[0].children[0];
                let context = result.contexts[index];
                let origin = result.contexts[input.0];
                assert_eq!(context.request, origin.request);
                assert_eq!(context.frame, origin.frame);
                assert!(context.iteration.is_some());
                if bytes.get(span.0..span.1) == Some(b"y") {
                    nested += 1;
                    assert!(origin.iteration.is_some(), "外側反復のRHSをrootへ戻さない");
                    assert_eq!(result.iterations[context.iteration.unwrap()].caller, origin);
                    let Some(Payload::Evaluation { value: rhs, .. }) =
                        &result.nodes[input.0].payload
                    else {
                        unreachable!()
                    };
                    assert_eq!(value, rhs, "元RHS Scalarをそのまま参照する");
                } else {
                    pattern += 1;
                    assert_eq!(origin.iteration, None);
                    let scalar = value.unwrap();
                    assert_eq!(result.nodes[scalar.0].arguments, vec![input]);
                    assert!(!result.nodes[input.0].scope.completions);
                    assert!(result.nodes[scalar.0].scope.completions);
                    rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar.0])
                        .unwrap();
                }
            }
            if matches!(&node.payload, Some(Payload::Scalar(_)))
                && matches!(&node.rule, Rule::Input { kind: "law", location: Location::Law { span } } if bytes.get(span.0..span.1) == Some(b"y+z"))
            {
                rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=index]).unwrap();
            }
        }
        assert_eq!((nested, pattern), (4, 2));
    }
    #[test]
    fn set_comprehension_captured_let_rejects_equal_foreign_iteration_request_and_call() {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(
                &[],
                r#"
 view captured(): Set<Set<Z>> = set { let y=10 in set { y+z | z in list<Z>[1] } | x in list<Z>[1,2] };
 view repeated(): (Set<Set<Z>>,Set<Set<Z>>) = (captured(),captured());
"#,
            ),
            &[
                "first=evaluate(Calc.captured)",
                "second=evaluate(Calc.captured)",
                "calls=evaluate(Calc.repeated)",
            ],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let bytes = result.prepared.inputs().sources().law().bytes();
        let aliases: Vec<_> = result
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                let Some(Payload::Evaluation {
                    expression, parts, ..
                }) = &node.payload
                else {
                    return None;
                };
                let Some(Payload::Expression {
                    location: Location::Law { span },
                    ..
                }) = &result.nodes[expression.0].payload
                else {
                    return None;
                };
                if bytes.get(span.0..span.1) == Some(b"y") {
                    Some((index, parts[0].children[0]))
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(aliases.len(), 8);
        for kind in 0..3 {
            let (target, original, foreign) = aliases
                .iter()
                .find_map(|&(target, original)| {
                    let own = result.contexts[original.0];
                    aliases.iter().find_map(|&(_, foreign)| {
                        let other = result.contexts[foreign.0];
                        let differs = match kind {
                            0 => {
                                own.request == other.request
                                    && own.frame == other.frame
                                    && own.iteration != other.iteration
                            }
                            1 => own.request != other.request && own.frame == other.frame,
                            _ => own.request == other.request && own.frame != other.frame,
                        };
                        (differs && foreign.0 < target).then_some((target, original, foreign))
                    })
                })
                .unwrap();
            assert_ne!(original, foreign);
            let Some(Payload::Evaluation {
                value: original_value,
                ..
            }) = &result.nodes[original.0].payload
            else {
                unreachable!()
            };
            let Some(Payload::Evaluation {
                value: foreign_value,
                ..
            }) = &result.nodes[foreign.0].payload
            else {
                unreachable!()
            };
            assert_eq!(
                data_scalar_at(&result, original_value.unwrap().0),
                data_scalar_at(&result, foreign_value.unwrap().0)
            );
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
            let mut changed = result.nodes[..=target].to_vec();
            let Some(Payload::Evaluation {
                expression,
                parts,
                value,
                ..
            }) = &mut changed[target].payload
            else {
                unreachable!()
            };
            parts[0].children = vec![foreign];
            parts[0].value = *foreign_value;
            *value = *foreign_value;
            let arguments = std::iter::once(*expression)
                .chain([foreign])
                .chain(*foreign_value)
                .collect();
            changed[target].arguments = arguments;
            rejects_named_prefix(&result, &changed);
        }
    }
    fn in_quantifier_fixture(omitted: &[&str]) -> InputSources {
        numeric_recheck_fixture(
            omitted,
            r#"
 view all(): Bool = forall n in list<Z>[1,1,2] . n>0;
 view empty(): Bool = exists q in list<Q>[] . q>rat(0,1);
 view negative(s: Sample): Bool = forall r in list<Sample>[s,s] . r.p;
 law required called(x: Sample): negative(x);
 law required both(x: Sample): negative(x) and negative(x);
 view echo(b: Bool): Bool = forall item in list<Bool>[b] . item;
 view argument_call(): Bool = echo(echo(true));
 view nested(): Bool = let y=1 in forall x in list<Z>[1,2] . exists z in set { k+1 | k in list<Z>[1,2] } . match x { held => z>held+y-1; };
 view observe(s: Sample): Q = s.q;
 view full(): Bool = forall n in list<Z>[1,2] . n>0;
 view early(): Bool = forall n in list<Z>[1,2] . n>1;
 view later(): Z = 9;
"#,
        )
    }
    fn in_quantifier_example(requests: &[&str]) -> ObservedEvaluation {
        evaluate_observed_bytes(
            in_quantifier_fixture(&[]),
            requests,
            &mut named_call_quiet(),
        )
        .unwrap()
    }
    #[test]
    fn in_quantifier_scope_rejects_duplicate_actual_domain_at_scalar_prefix() {
        let result = in_quantifier_example(&["capture=evaluate(Calc.nested)"]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let scalar = result.nodes.iter().enumerate().find_map(|(index, node)| {
            (result.contexts[index].iteration.is_none()
                && matches!(&node.payload, Some(Payload::Scalar(Scalar::Bool(_))))
                && matches!(&node.rule, Rule::Input { kind: "law", location: Location::Law { span } }
                    if result.prepared.inputs().sources().law().bytes()[span.0..span.1].starts_with(b"forall x in")))
                .then_some(index)
        }).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
        let original = &result.nodes[scalar].scope;
        let inner: Vec<_> = original
            .quantifiers
            .iter()
            .enumerate()
            .filter_map(|(index, q)| (q.name == "z").then_some(index))
            .collect();
        assert_eq!(inner.len(), 2);
        assert_eq!(
            original.quantifiers[inner[0]].occurrence,
            original.quantifiers[inner[1]].occurrence
        );
        assert_ne!(
            original.quantifiers[inner[0]].domain,
            original.quantifiers[inner[1]].domain
        );
        assert_ne!(
            original.quantifiers[inner[0]].context,
            original.quantifiers[inner[1]].context
        );
        let mut reordered = result.nodes[..=scalar].to_vec();
        reordered[scalar].scope.quantifiers.swap(inner[0], inner[1]);
        assert_eq!(&reordered[scalar].scope, original);
        assert_eq!(original, &reordered[scalar].scope);
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        let mut changed = result.nodes[..=scalar].to_vec();
        changed[scalar].scope.quantifiers[inner[1]] = original.quantifiers[inner[0]].clone();
        assert_ne!(&changed[scalar].scope, original);
        assert_ne!(original, &changed[scalar].scope);
        rejects_named_prefix(&result, &changed);
        // 拒否対象は未完成Scalarまで。完成Answer受理をこの改変からは主張しない。
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
    }
    #[test]
    fn in_quantifier_domain_nesting_keeps_ast_order_across_callee_definitions() {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(&[], r#"
 view early_domain(flag: Bool): Bool = exists early in list<Bool>[flag] . early;
 view from_early(): Bool = forall outside in list<Bool>[early_domain((exists argument in list<Z>[1] . argument=1))] . outside;
 view domain_nested(): Bool = forall x in list<Bool>[(exists y in list<Z>[1] . y=1)] . x;
 view branch_nested(): Bool = forall n in (if (forall b in list<Bool>[true] . b) then list<Z>[1] else list<Z>[]) . n>0;
 view from_late(): Bool = forall outside in list<Bool>[late_domain((exists argument in list<Z>[1] . argument=1))] . outside;
 view late_domain(flag: Bool): Bool = exists late in list<Bool>[flag] . late;
"#),
            &["direct=evaluate(Calc.domain_nested)", "branch=evaluate(Calc.branch_nested)",
              "before=evaluate(Calc.from_early)", "after=evaluate(Calc.from_late)"],
            &mut named_call_quiet(),
        ).unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let expected = [
            vec!["x", "y"],
            vec!["n", "b"],
            vec!["outside", "argument", "early"],
            vec!["outside", "argument", "late"],
        ];
        for (request, names) in expected.iter().enumerate() {
            let answer = &result.answers[request];
            assert_eq!(
                data_scalar_at(&result, answer.outputs["value"].0),
                &Scalar::Bool(true)
            );
            let scalar = answer.outputs["value"].0;
            let quantifiers = &result.nodes[scalar].scope.quantifiers;
            assert_eq!(
                quantifiers
                    .iter()
                    .map(|q| q.name.as_str())
                    .collect::<Vec<_>>(),
                *names
            );
            assert!(quantifiers.iter().all(|q| q.domain.is_some()));
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
            let outer = quantifiers[0].occurrence;
            let targets: Vec<_> = result.nodes.iter().enumerate().filter_map(|(index,node)| {
                (result.contexts[index].request == request
                    && result.contexts[index].frame.is_none()
                    && result.contexts[index].iteration.is_none()
                    && node.scope.quantifiers.first().is_some_and(|q| q.occurrence == outer)
                    && (matches!(&node.rule, Rule::Input {kind:"law",location:Location::Law {span}} if *span==outer)
                        || matches!(&node.payload, Some(Payload::Domain {..}))
                        || matches!(&node.payload, Some(Payload::Evaluation {..}))))
                    .then_some(index)
            }).collect();
            assert!(targets.iter().any(|index| *index == scalar));
            assert!(
                targets
                    .iter()
                    .any(|index| result.nodes[*index].ty == NodeType::Domain)
            );
            assert!(targets.iter().any(|index| matches!(
                &result.nodes[*index].payload,
                Some(Payload::Expression { .. })
            )));
            assert!(targets.iter().any(|index| matches!(
                &result.nodes[*index].payload,
                Some(Payload::Evaluation { .. })
            )));
            for target in targets {
                assert_eq!(
                    result.nodes[target]
                        .scope
                        .quantifiers
                        .iter()
                        .map(|q| q.name.as_str())
                        .collect::<Vec<_>>(),
                    *names
                );
                rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
                let mut changed = result.nodes[..=target].to_vec();
                changed[target].scope.quantifiers.swap(0, 1);
                rejects_named_prefix(&result, &changed);
            }
        }
    }
    fn in_domain(result: &ObservedEvaluation, request: usize) -> usize {
        result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (result.contexts[index].request == request && node.ty == NodeType::Domain)
                    .then_some(index)
            })
            .unwrap()
    }
    fn finite_instances(nodes: &mut [Node], index: usize, instances: Vec<NodeRef>) {
        let source = nodes[index].arguments[0];
        let Some(Payload::FiniteExhaustion {
            domain,
            instances: actual,
            ..
        }) = &mut nodes[index].payload
        else {
            unreachable!()
        };
        *actual = instances.clone();
        let domain = *domain;
        nodes[index].arguments = std::iter::once(source)
            .chain([domain])
            .chain(instances)
            .collect();
    }
    #[test]
    fn in_quantifier_prefixes_recheck_domain_elements_type_source_and_scope() {
        let result = in_quantifier_example(&[
            "first=evaluate(Calc.all)",
            "again=evaluate(Calc.all)",
            "empty=evaluate(Calc.empty)",
        ]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert_eq!(
            data_scalar_at(&result, result.answers[0].outputs["value"].0),
            &Scalar::Bool(true)
        );
        assert_eq!(
            data_scalar_at(&result, result.answers[2].outputs["value"].0),
            &Scalar::Bool(false)
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let domain = in_domain(&result, 0);
        let Some(Payload::Domain { elements, .. }) = &result.nodes[domain].payload else {
            unreachable!()
        };
        assert_eq!(elements.len(), 2);
        let member = elements[0].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=member]).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=domain]).unwrap();
        for mutation in 0..2 {
            let mut changed = result.nodes[..=member].to_vec();
            if mutation == 0 {
                changed[member].payload = Some(Payload::Scalar(Scalar::Z(3.into())));
            } else {
                changed[member].payload = Some(Payload::Scalar(Scalar::Q(1.into(), 1.into())));
                changed[member].ty = NodeType::Value(Type::Q);
            }
            rejects_named_prefix(&result, &changed);
        }
        for mutation in 0..3 {
            let mut changed = result.nodes[..=domain].to_vec();
            let Some(Payload::Domain { ty, elements }) = &mut changed[domain].payload else {
                unreachable!()
            };
            match mutation {
                0 => *ty = Type::Q,
                1 => {
                    elements.pop();
                }
                _ => {
                    elements[1] = elements[0];
                }
            }
            let members = elements.clone();
            let mut arguments = changed[domain].arguments[..2].to_vec();
            arguments.extend(members);
            changed[domain].arguments = arguments;
            rejects_named_prefix(&result, &changed);
        }
        let source = result.nodes[domain].arguments[0].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source]).unwrap();
        let mut changed = result.nodes[..=source].to_vec();
        changed[source].scope.quantifiers[0].kind = crate::law::ast::QuantKind::Exists;
        rejects_named_prefix(&result, &changed);
        let scalar = result.answers[1].outputs["value"].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
        let mut changed = result.nodes[..=scalar].to_vec();
        changed[scalar].scope.quantifiers[0].domain = Some(NodeRef(domain));
        rejects_named_prefix(&result, &changed);
        let mut changed = result.nodes[..=scalar].to_vec();
        changed[scalar].scope.completions = true;
        rejects_named_prefix(&result, &changed);
        let mut changed = result.nodes[..=scalar].to_vec();
        changed[scalar].support.push(Fact {
            snapshot: "v".into(),
            subject: "sample".into(),
            field: Some("Numeric.Sample.p".into()),
            atom: Some("p".into()),
        });
        rejects_named_prefix(&result, &changed);
    }
    #[test]
    fn in_quantifier_exhaustion_rechecks_coverage_body_kind_and_binder_at_prefix() {
        let mut result = in_quantifier_example(&[
            "value=evaluate(Calc.all)",
            "nested=evaluate(Calc.nested)",
            "argument=evaluate(Calc.argument_call)",
        ]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert_eq!(
            result.answers[2].scope.quantifiers.len(),
            2,
            "同じcallee量化ASTでも引数callと外側callの実域を保持する"
        );
        assert_ne!(
            result.answers[2].scope.quantifiers[0].context,
            result.answers[2].scope.quantifiers[1].context
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let proof = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(&node.payload, Some(Payload::FiniteExhaustion { .. })).then_some(index)
            })
            .unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=proof]).unwrap();
        let Some(Payload::FiniteExhaustion { instances, .. }) = &result.nodes[proof].payload else {
            unreachable!()
        };
        let instances = instances.clone();
        let mut reordered = result.nodes[..=proof].to_vec();
        let mut reverse = instances.clone();
        reverse.reverse();
        finite_instances(&mut reordered, proof, reverse);
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        for mutation in 0..3 {
            let mut changed = result.nodes[..=proof].to_vec();
            if mutation == 0 {
                let Some(Payload::FiniteExhaustion { checked, .. }) = &mut changed[proof].payload
                else {
                    unreachable!()
                };
                *checked += 1;
            } else {
                let mut bodies = instances.clone();
                if mutation == 1 {
                    bodies.pop();
                } else {
                    bodies[1] = bodies[0];
                }
                finite_instances(&mut changed, proof, bodies);
            }
            rejects_named_prefix(&result, &changed);
        }
        let mut changed = result.nodes[..=proof].to_vec();
        changed[proof].scope.quantifiers[0].kind = crate::law::ast::QuantKind::Exists;
        rejects_named_prefix(&result, &changed);
        let binder = iteration_binder_scalar_for_name(&result, 1, b"n");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=binder]).unwrap();
        let old = result.iterations[1].member.clone();
        result.iterations[1].member = super::super::call::Member::SetElement(Scalar::Z(1.into()));
        rejects_named_prefix(&result, &result.nodes[..=binder]);
        result.iterations[1].member = old;
        let body_value = match &result.nodes[instances[0].0].payload {
            Some(Payload::Evaluation {
                value: Some(value), ..
            }) => value.0,
            _ => unreachable!(),
        };
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=body_value]).unwrap();
        let mut changed = result.nodes[..=body_value].to_vec();
        changed[body_value].payload = Some(Payload::Scalar(Scalar::Bool(false)));
        rejects_named_prefix(&result, &changed);
        let root = result.answers[0].outputs["value"].0;
        let mut changed = result.nodes[..=root].to_vec();
        changed[root].evidence.clear();
        rejects_named_prefix(&result, &changed);
        let nested_proof = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (result.contexts[index].request == 1
                    && matches!(&node.payload, Some(Payload::FiniteExhaustion { .. })))
                .then_some(index)
            })
            .unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=nested_proof]).unwrap();
        let Some(Payload::FiniteExhaustion { instances, .. }) = &result.nodes[nested_proof].payload
        else {
            unreachable!()
        };
        let mut reverse = instances.clone();
        reverse.reverse();
        let mut reordered = result.nodes.clone();
        finite_instances(&mut reordered, nested_proof, reverse);
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        let display = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (result.contexts[index].request == 1
                    && matches!(&node.payload, Some(Payload::Scalar(Scalar::Set { .. }))))
                .then_some(index)
            })
            .unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=display]).unwrap();
        let mut reordered = result.nodes.clone();
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut reordered[display].payload
        else {
            unreachable!()
        };
        items.reverse();
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
    fn iteration_binder_scalar_for_name(
        result: &ObservedEvaluation,
        iteration: usize,
        name: &[u8],
    ) -> usize {
        result.nodes.iter().enumerate().find_map(|(index,node)|{
            (result.contexts[index].iteration==Some(iteration) && matches!(&node.payload,Some(Payload::Scalar(_))) && matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span}} if result.prepared.inputs().sources().law().bytes().get(span.0..span.1)==Some(name))).then_some(index)
        }).unwrap()
    }
    #[test]
    fn in_quantifier_callee_counterexamples_keep_actual_formals_and_reject_foreign_producers() {
        let result = in_quantifier_example(&[
            "first=check(Calc.called,x=@v/sample)",
            "again=check(Calc.called,x=@v/sample)",
            "both=check(Calc.both,x=@v/sample)",
        ]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert!(
            result
                .answers
                .iter()
                .all(|answer| answer.status == Decision::Refuted)
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let counters: Vec<_> = result
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                (node.arguments.len() == 3
                    && matches!(&node.payload, Some(Payload::Counterexample { .. })))
                .then_some(index)
            })
            .collect();
        assert_eq!(counters.len(), 4);
        for counter in &counters {
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=*counter]).unwrap();
            let Some(Payload::Counterexample { bindings, left, .. }) =
                &result.nodes[*counter].payload
            else {
                unreachable!()
            };
            assert_eq!(
                bindings.iter().map(|b| b.name.as_str()).collect::<Vec<_>>(),
                vec!["s", "r"]
            );
            assert_eq!(data_scalar_at(&result, left.0), &Scalar::Bool(false));
            assert!(
                result.answers[result.contexts[*counter].request]
                    .evidence
                    .contains(&NodeRef(*counter))
            );
        }
        let target = counters[1];
        let foreign = counters[0];
        let Some(Payload::Counterexample {
            bindings: original,
            left: old_left,
            right: old_right,
            ..
        }) = &result.nodes[foreign].payload
        else {
            unreachable!()
        };
        for mutation in 0..3 {
            let mut changed = result.nodes[..=target].to_vec();
            let Some(Payload::Counterexample {
                bindings,
                left,
                right,
                ..
            }) = &mut changed[target].payload
            else {
                unreachable!()
            };
            match mutation {
                0 => bindings[1].value = original[1].value,
                1 => *left = *old_left,
                _ => *right = *old_right,
            }
            rejects_named_prefix(&result, &changed);
        }
        let mut changed = result.nodes[..=target].to_vec();
        changed[target].arguments = result.nodes[foreign].arguments.clone();
        changed[target].payload = result.nodes[foreign].payload.clone();
        changed[target].scope = result.nodes[foreign].scope.clone();
        rejects_named_prefix(&result, &changed);
        let target = counters[3];
        let foreign = counters[2];
        assert_eq!(
            result.contexts[target].request,
            result.contexts[foreign].request
        );
        assert_ne!(
            result.contexts[target].frame,
            result.contexts[foreign].frame
        );
        let Some(Payload::Counterexample { left: own, .. }) = &result.nodes[target].payload else {
            unreachable!()
        };
        let Some(Payload::Counterexample { left: other, .. }) = &result.nodes[foreign].payload
        else {
            unreachable!()
        };
        assert_eq!(
            data_scalar_at(&result, own.0),
            data_scalar_at(&result, other.0)
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
        let mut changed = result.nodes[..=target].to_vec();
        changed[target].arguments = result.nodes[foreign].arguments.clone();
        changed[target].payload = result.nodes[foreign].payload.clone();
        changed[target].scope = result.nodes[foreign].scope.clone();
        rejects_named_prefix(&result, &changed);
    }
    #[test]
    fn in_quantifier_actual_domain_body_and_exhaustion_phases_preserve_stops() {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{
            cell::{Cell, RefCell},
            rc::Rc,
        };
        for (operation, view, stop) in [
            ("quant_domain", "full", 0),
            ("quant_body", "early", 1),
            ("quant_exhaustion", "full", 2),
        ] {
            let sources = in_quantifier_fixture(&["q"]);
            let current = format!("current=evaluate(Calc.{view})");
            let asks = [
                "seed=evaluate(Calc.later)",
                "prior=check(Calc.called,x=@v/sample)",
                "hole=evaluate(Calc.observe,s=@v/sample)",
                current.as_str(),
                "later=evaluate(Calc.later)",
            ];
            let mut normal_control = named_call_quiet();
            let prepared = prepare_observed(sources.clone(), &asks, &mut normal_control).unwrap();
            let Signature::View { body, .. } =
                &prepared.inputs().law().declarations[&format!("Calc.{view}")].signature
            else {
                unreachable!()
            };
            let target = prepared.inputs().law().exprs[*body].span;
            let context = super::super::call::Context {
                request: 3,
                frame: None,
                iteration: None,
            };
            let progress = Rc::new(RefCell::new(Vec::new()));
            let progress_clone = progress.clone();
            let normal = evaluate_observed_with_validator(
                prepared,
                &mut normal_control,
                |environment, graph, request, answer| {
                    environment.validate_answer(graph, request, answer)?;
                    if request.id == "hole" {
                        let progress = progress_clone.clone();
                        data::observe_iterations(move |span, actual, phase, index| {
                            if span == target && actual == context && phase == operation {
                                progress.borrow_mut().push(index);
                            }
                        });
                    }
                    Ok(())
                },
            );
            data::clear_iteration_observer();
            let normal = normal.unwrap();
            assert_eq!(normal.status(), "partial", "{:?}", normal.issues);
            assert_eq!(normal.answers[1].status, Decision::Refuted);
            assert_eq!(normal.answers[3].status, Decision::Established);
            assert_eq!(
                &*progress.borrow(),
                if operation == "quant_exhaustion" {
                    &[0, 1, 2][..]
                } else {
                    &[0, 1][..]
                }
            );
            rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
            let Json::Obj(ref normal_wire) = normal.wire() else {
                unreachable!()
            };
            let Json::Arr(normal_answers) = &normal_wire["answers"] else {
                unreachable!()
            };
            let (limits, usage, expected) = match stop {
                0 => (
                    Limits::default(),
                    Usage {
                        signal: Some(Signal::Term),
                        ..Usage::default()
                    },
                    StopReason::Cancelled(Signal::Term),
                ),
                1 => (
                    Limits {
                        time_ms: Some(3),
                        memory_mib: None,
                    },
                    Usage {
                        elapsed_ms: 4,
                        ..Usage::default()
                    },
                    StopReason::BudgetExhausted {
                        resource: Resource::TimeMs,
                        limit: 3,
                        observed: 4,
                    },
                ),
                _ => (
                    Limits {
                        time_ms: None,
                        memory_mib: Some(7),
                    },
                    Usage {
                        memory_mib: 8,
                        ..Usage::default()
                    },
                    StopReason::BudgetExhausted {
                        resource: Resource::MemoryMib,
                        limit: 7,
                        observed: 8,
                    },
                ),
            };
            let armed = Rc::new(Cell::new(false));
            let probes = Rc::new(Cell::new(0));
            let frozen = Rc::new(Cell::new(None));
            let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
            let mut control = Control::new(limits, move |checkpoint| {
                count.set(count.get() + 1);
                if arm.replace(false) {
                    assert_eq!(checkpoint, Checkpoint::FiniteIteration);
                    assert!(freeze.replace(Some(count.get())).is_none());
                    usage
                } else {
                    Usage::default()
                }
            });
            let prepared = prepare_observed(sources, &asks, &mut control).unwrap();
            let seen = Rc::new(RefCell::new(Vec::new()));
            let observed = seen.clone();
            let stopped = evaluate_observed_with_validator(
                prepared,
                &mut control,
                |environment, graph, request, answer| {
                    environment.validate_answer(graph, request, answer)?;
                    if request.id == "hole" {
                        let (observed, armed) = (observed.clone(), armed.clone());
                        data::observe_iterations(move |span, actual, phase, index| {
                            if span == target && actual == context && phase == operation {
                                observed.borrow_mut().push(index);
                                if index == 1 {
                                    armed.set(true);
                                }
                            }
                        });
                    }
                    Ok(())
                },
            );
            data::clear_iteration_observer();
            let stopped = stopped.unwrap();
            assert_eq!(&*seen.borrow(), &[0, 1]);
            assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
            assert_eq!(control.stop_reason(), Some(expected.clone()));
            assert_eq!(Some(probes.get()), frozen.get());
            let Json::Obj(ref wire) = stopped.wire() else {
                unreachable!()
            };
            let Json::Arr(answers) = &wire["answers"] else {
                unreachable!()
            };
            assert_eq!(&answers[..3], &normal_answers[..3]);
            for answer in &stopped.answers[3..] {
                assert_eq!(answer.status, Decision::Undetermined);
                assert!(answer.outputs.is_empty());
                assert!(answer.reasons.iter().any(
                    |reason| matches!(&reason.kind,ReasonKind::Stop(actual) if actual==&expected)
                ));
                let Json::Obj(ref expected_wire) = expected.wire() else {
                    unreachable!()
                };
                let reason=answer.reasons.iter().find(|reason|matches!(&reason.kind,ReasonKind::Stop(actual) if actual==&expected)).unwrap();
                let Json::Obj(ref reason_wire) = reason.wire() else {
                    unreachable!()
                };
                assert_eq!(reason_wire.get("details"), expected_wire.get("details"));
            }
            assert!(
                !stopped
                    .nodes
                    .iter()
                    .enumerate()
                    .any(|(index, node)| stopped.contexts[index].request == 3
                        && matches!(&node.payload, Some(Payload::FiniteExhaustion { .. })))
            );
            if operation == "quant_body" {
                assert!(
                    stopped
                        .nodes
                        .iter()
                        .enumerate()
                        .any(|(index, node)| stopped.contexts[index].request == 3
                            && matches!(&node.payload, Some(Payload::Counterexample { .. })))
                );
            }
            rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
            let before = probes.get();
            assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
            assert_eq!(probes.get(), before);
        }
    }
}
