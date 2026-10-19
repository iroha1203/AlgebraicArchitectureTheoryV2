//! 明示束縛の参照・原始 field と Z/Bool 演算を原 AST から評価する。
#[path = "term_comparison_evaluate.rs"]
mod term_comparison_evaluate;
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
#[path = "answer_projection_condition_evaluate.rs"]
mod answer_projection_condition;
#[path = "completion_evaluate.rs"]
mod completion;
#[path = "dependent_family_evaluate.rs"]
mod dependent_family;
#[path = "family_evaluate.rs"]
mod family;
#[path = "owned_call_evaluate.rs"]
mod owned_call;
#[path = "owned_family_evaluate.rs"]
mod owned_family;
#[path = "owned_type_evaluate.rs"]
mod owned_type;
#[path = "universal_evaluate.rs"]
mod universal;

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
    condition_failed: bool,
    condition_pending: bool,
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
    // 補完開始前に元Controlで独立検査を終えた回答だけを、停止時に保持する。
    verified_observed: Option<Answer>,
    completing: bool,
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
    /// 欠測を含む元算術が定数になる場合だけ、元出現と実子評価から通常値を作る。
    fn affine_constant(
        &mut self,
        span: (usize, usize),
        ty: &Type,
        children: &[&Evaluated],
    ) -> Result<Option<NodeRef>, Failure> {
        if !(numeric::is_numeric_type(ty, self.control)? || *ty == Type::Bool) {
            return Ok(None);
        }
        let source = self
            .sources
            .get(&span)
            .cloned()
            .ok_or_else(|| Failure::Internal("算術の元Sourceがない".into()))?;
        let Some(known) = source.known_value else {
            return Ok(None);
        };
        if known.ty() != *ty {
            return Err(Failure::Internal("元算術の確定値の型が違う".into()));
        }
        let mut scope = source.scope;
        let mut support = vec![];
        for child in children {
            self.tick(Checkpoint::FiniteIteration)?;
            scope.merge(&child.scope);
            support.extend(child.support.iter().cloned());
            self.tick(Checkpoint::FiniteIteration)?;
        }
        support.sort();
        support.dedup();
        let arguments = std::iter::once(source.expression)
            .chain(children.iter().map(|child| child.evaluation))
            .collect();
        let value = self.value(
            known,
            Rule::Input {
                kind: "law",
                location: Location::Law { span },
            },
            arguments,
            support,
            scope,
        )?;
        #[cfg(test)]
        data::observe_actual(span, self.graph.active, "affine_scalar", 1);
        self.tick(Checkpoint::FiniteIteration)?;
        Ok(Some(value))
    }
    /// 元左右は欠測のまま保持し、差の全係数が消えた比較だけを導出する。
    fn affine_equality(
        &mut self,
        span: (usize, usize),
        ty: &Type,
        left: &Evaluated,
        right: &Evaluated,
    ) -> Result<Option<(NodeRef, NodeRef)>, Failure> {
        if !numeric::is_numeric_type(ty, self.control)? {
            return Ok(None);
        }
        let source = self
            .sources
            .get(&span)
            .cloned()
            .ok_or_else(|| Failure::Internal("アフィン比較の元Sourceがない".into()))?;
        let Some(known @ Scalar::Bool(_)) = source.known_value else {
            return Ok(None);
        };
        let Some((expected, residual)) =
            self.environment
                .affine_comparison(self.graph, span, &self.bindings)?
        else {
            return Err(Failure::Internal("元比較の定数残差が再構成できない".into()));
        };
        if known != expected || residual.ty() != *ty {
            return Err(Failure::Internal("元比較の定数残差・Bool型が違う".into()));
        }
        let own = source.expression;
        let mut scope = source.scope;
        scope.merge(&left.scope);
        scope.merge(&right.scope);
        let mut support = left.support.clone();
        support.extend(right.support.iter().cloned());
        support.sort();
        support.dedup();
        let difference = self.push(Node {
            ty: NodeType::Expression(ty.clone()),
            payload: Some(Payload::Transform {
                operation: TransformOp::Difference,
                operands: vec![left.expression, right.expression],
                bindings: self.bindings.clone(),
            }),
            rule: Rule::Construction("expression"),
            arguments: vec![own, left.evaluation, right.evaluation],
            support: support.clone(),
            evidence: vec![],
            judgment: None,
            scope: scope.clone(),
            reasons: vec![],
        })?;
        #[cfg(test)]
        data::observe_actual(span, self.graph.active, "affine_comparison", 0);
        self.tick(Checkpoint::FiniteIteration)?;
        let residual = self.value(
            residual,
            Rule::Construction("evaluation"),
            vec![difference, own, left.evaluation, right.evaluation],
            support.clone(),
            scope.clone(),
        )?;
        #[cfg(test)]
        data::observe_actual(span, self.graph.active, "affine_comparison", 1);
        self.tick(Checkpoint::FiniteIteration)?;
        let normalization = self.push(Node {
            ty: NodeType::Evidence,
            payload: Some(Payload::Normalization {
                before: difference,
                after: residual,
                steps: vec![left.expression, right.expression, difference],
            }),
            rule: Rule::Construction("evidence"),
            arguments: vec![own, left.evaluation, right.evaluation, difference, residual],
            support: support.clone(),
            evidence: vec![],
            judgment: None,
            scope: scope.clone(),
            reasons: vec![],
        })?;
        #[cfg(test)]
        data::observe_actual(span, self.graph.active, "affine_comparison", 2);
        self.tick(Checkpoint::FiniteIteration)?;
        let value = self.push(Node {
            ty: NodeType::Value(Type::Bool),
            payload: Some(Payload::Scalar(known)),
            rule: Rule::Input {
                kind: "law",
                location: Location::Law { span },
            },
            arguments: vec![
                own,
                left.evaluation,
                right.evaluation,
                difference,
                residual,
                normalization,
            ],
            support,
            evidence: vec![normalization],
            judgment: None,
            scope,
            reasons: vec![],
        })?;
        #[cfg(test)]
        data::observe_actual(span, self.graph.active, "affine_comparison", 3);
        self.tick(Checkpoint::FiniteIteration)?;
        Ok(Some((value, residual)))
    }
    fn bind(&mut self, params: &[Param]) -> Result<(), Failure> {
        self.bind_parameters(params, false)
    }
    fn bind_parameters(&mut self, params: &[Param], defer_owned: bool) -> Result<(), Failure> {
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
                        if constraint.parameter == p.name
                            && constraint.dynamic
                            && !self.environment.fixed_owned_binding(self.request, p)?
                            && !(defer_owned && matches!(p.ty, Type::Owned(..)))
                        {
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
                    if let Some(node) =
                        self.environment
                            .owned_binding_node(self.graph, self.request, p, r)?
                    {
                        let value = self.push(node)?;
                        self.base.merge(&self.graph.get(value)?.scope);
                    }
                    self.bindings.push(Binding {
                        name: p.name.clone(),
                        value: r,
                        ty: p.ty.erase(),
                    });
                }
                Selector::Answer { .. } => {
                    if p.ty != p.ty.erase()
                        && !self.environment.fixed_owned_binding(self.request, p)?
                        && !(defer_owned
                            && self.environment.deferred_owned_binding(self.request, p)?)
                        && self
                            .request
                            .constraints
                            .iter()
                            .any(|constraint| constraint.parameter == p.name && constraint.dynamic)
                    {
                        return Err(self.unsupported(p.span, "Answer束縛の動的owner制約"));
                    }
                    let plan =
                        self.environment
                            .answer_binding(self.graph, &argument.value, p.span)?;
                    let actual = match &plan {
                        super::environment::AnswerBinding::Reference(value) => {
                            self.graph.get(*value)?.ty.clone()
                        }
                        super::environment::AnswerBinding::Projection(node) => node.ty.clone(),
                        super::environment::AnswerBinding::Inapplicable(_) => {
                            return Err(self.unsupported(p.span, "自由族のAnswer射影条件"));
                        }
                    };
                    if actual != NodeType::Value(p.ty.erase()) {
                        return Err(self.unsupported(p.span, "Answer構造成分の動的型不適合"));
                    }
                    let value = match plan {
                        super::environment::AnswerBinding::Reference(value) => value,
                        super::environment::AnswerBinding::Projection(node) => self.push(node)?,
                        super::environment::AnswerBinding::Inapplicable(_) => {
                            return Err(self.unsupported(p.span, "自由族のAnswer射影条件"));
                        }
                    };
                    if let Some(node) =
                        self.environment
                            .owned_binding_node(self.graph, self.request, p, value)?
                    {
                        let check = self.push(node)?;
                        self.base.merge(&self.graph.get(check)?.scope);
                    }
                    self.base.merge(&self.graph.get(value)?.scope);
                    self.bindings.push(Binding {
                        name: p.name.clone(),
                        value,
                        ty: p.ty.erase(),
                    });
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
            condition_failed,
            condition_pending,
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
                    condition_failed,
                    condition_pending,
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
                        && let Some((_, value)) = self.environment.type_iteration_argument(
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
                    let mut owner = self.source(first.span, parameter)?;
                    // 元の各 token prefix を、その prefix 自身の検査済み型と範囲で
                    // commit する。最終型を中間 Ref の型として流用しない。
                    for (_index, (prefix, prefix_ty)) in self
                        .environment
                        .dotted_prefixes(id)?
                        .into_iter()
                        .enumerate()
                        .skip(1)
                    {
                        self.tick(Checkpoint::FiniteIteration)?;
                        if !(owner.condition_failed || owner.condition_pending)
                            && !matches!(owner.known_value, Some(Scalar::Subject { .. }))
                        {
                            return Err(self.unsupported(prefix, "未確定の参照からの field 読取り"));
                        }
                        if !matches!(prefix_ty, Type::Bool | Type::Ref(_) | Type::Owned(_, _))
                            && !data::supported(
                                &prefix_ty,
                                self.environment.inputs.law(),
                                self.control,
                            )?
                        {
                            return Err(self.unsupported(prefix, "Z/Bool/Ref 以外の原始 slot 評価"));
                        }
                        owner = self.source(prefix, prefix_ty)?;
                        #[cfg(test)]
                        data::observe_actual(span, self.graph.active, "field_prepare", _index);
                        self.tick(Checkpoint::FiniteIteration)?;
                    }
                }
                ExprKind::Field { base, .. } => {
                    let owner = self.prepare_source(*base)?;
                    if !(owner.condition_failed || owner.condition_pending)
                        && !matches!(owner.known_value, Some(Scalar::Subject { .. }))
                    {
                        return Err(self.unsupported(span, "未確定の参照からの field 読取り"));
                    }
                    if !matches!(ty, Type::Bool | Type::Ref(_) | Type::Owned(_, _))
                        && !data::supported(&ty, self.environment.inputs.law(), self.control)?
                    {
                        return Err(self.unsupported(span, "Z/Bool/Ref 以外の原始 slot 評価"));
                    }
                }
                ExprKind::Quant { .. } => {
                    if self
                        .environment
                        .universal_quantifier_plan(self.graph, id, &self.bindings)?
                        .is_none()
                    {
                        let spec = super::quantifier::spec(
                            self.environment.inputs.law(),
                            id,
                            self.control,
                        )?;
                        if let Some(domain) = spec.domain {
                            self.prepare_source_child(domain)?;
                        }
                    }
                }
                ExprKind::SetComp { domain, .. } => {
                    self.prepare_source_child(*domain)?;
                }
                ExprKind::Family { owner, .. } => {
                    self.prepare_source_child(*owner)?;
                }
                ExprKind::Match { scrutinee, .. } => {
                    self.prepare_source_child(*scrutinee)?;
                }
                ExprKind::Group(child) => {
                    self.prepare_source_child(*child)?;
                }
                ExprKind::Let { value, body, .. } => {
                    self.prepare_source_child(*value)?;
                    self.prepare_source_child(*body)?;
                }
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    self.prepare_source_child(*cond)?;
                    self.prepare_source_child(*then_branch)?;
                    self.prepare_source_child(*else_branch)?;
                }
                ExprKind::Unary { op, operand }
                    if (*op == UnOp::Neg && numeric::is_numeric_type(&ty, self.control)?)
                        || (*op == UnOp::Not && ty == Type::Bool) =>
                {
                    self.prepare_source_child(*operand)?;
                }
                ExprKind::Binary { op, lhs, rhs } => {
                    let input_ty = self
                        .environment
                        .inputs
                        .law()
                        .expr_type(*lhs)
                        .ok_or_else(|| Failure::Internal("二項演算の型".into()))?;
                    if !supports_binary(*op, input_ty, self.environment.inputs.law(), self.control)?
                    {
                        return Err(self.unsupported(span, "対応済み Z/Bool 二項演算以外"));
                    }
                    self.prepare_source_child(*lhs)?;
                    self.prepare_source_child(*rhs)?;
                }
                ExprKind::Call { args, .. } if self.environment.named_view(id)?.is_some() => {
                    for &argument in args {
                        self.tick(Checkpoint::FiniteIteration)?;
                        self.prepare_source_child(argument)?;
                    }
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
                        .ok_or_else(|| self.unsupported(span, "数値組・射影・rat 以外の構成"))?;
                    for child in children {
                        self.tick(Checkpoint::FiniteIteration)?;
                        self.prepare_source_child(child)?;
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
        self.finish_with_reasons(
            span,
            ty,
            value,
            children,
            own_support,
            missing,
            comparison,
            residual,
            vec![],
        )
    }
    #[allow(clippy::too_many_arguments)]
    fn finish_with_reasons(
        &mut self,
        span: (usize, usize),
        ty: Type,
        value: Option<NodeRef>,
        children: Vec<Evaluated>,
        own_support: Vec<Fact>,
        missing: Option<Fact>,
        comparison: Option<(NodeRef, NodeRef)>,
        residual: Option<NodeRef>,
        reasons: Vec<Reason>,
    ) -> Result<Evaluated, Failure> {
        self.finish_with_evidence(
            span,
            ty,
            value,
            children,
            own_support,
            missing,
            comparison,
            residual,
            reasons,
            vec![],
        )
    }
    // 値が未生成でも、量化の正常instanceから既に得た反例を残す。
    #[allow(clippy::too_many_arguments)]
    fn finish_with_evidence(
        &mut self,
        span: (usize, usize),
        ty: Type,
        value: Option<NodeRef>,
        children: Vec<Evaluated>,
        own_support: Vec<Fact>,
        missing: Option<Fact>,
        comparison: Option<(NodeRef, NodeRef)>,
        residual: Option<NodeRef>,
        mut reasons: Vec<Reason>,
        partial_evidence: Vec<NodeRef>,
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
        for child in &children {
            self.tick(Checkpoint::FiniteIteration)?;
            support.extend(child.support.iter().cloned());

            self.tick(Checkpoint::FiniteIteration)?;
        }
        reasons.extend(self.environment.evaluation_child_reasons(
            self.graph,
            expression,
            &children.iter().map(|c| c.evaluation).collect::<Vec<_>>(),
        )?);
        support.sort();
        support.dedup();
        if let Some(reason) = source.missing {
            reasons.push(reason);
        }
        let child_refs: Vec<_> = children.iter().map(|c| c.evaluation).collect();
        if let Some(reason) =
            self.environment
                .term_algorithm_reason(self.graph, expression, &child_refs)?
        {
            reasons.push(reason);
        }
        sort_reasons(&mut reasons);
        let evidence = if let Some(value) = value {
            if !partial_evidence.is_empty() {
                return Err(Failure::Internal("確定値に部分証拠を重ねている".into()));
            }
            self.graph.get(value)?.evidence.clone()
        } else {
            partial_evidence
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
            if matches!(
                self.environment.inputs.law().exprs[id].kind,
                ExprKind::Quant { .. }
            ) && let Some(plan) =
                self.environment
                    .universal_quantifier_plan(self.graph, id, &self.bindings)?
            {
                let value = self.universal_evaluation(plan)?.evaluated;
                self.completed.insert(id, value.clone());
                self.tick(Checkpoint::Expression)?;
                return Ok(value);
            }
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
            #[cfg(test)]
            if matches!(
                self.environment.inputs.law().exprs[id].kind,
                ExprKind::Call { .. }
            ) {
                data::observe_actual(
                    self.environment.inputs.law().exprs[id].span,
                    self.graph.active,
                    "call_evaluation_complete",
                    0,
                );
            }
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
                let mut current = if let Some((domain, known)) = self
                    .environment
                    .type_iteration_argument(self.graph, first.span, &first.name, &self.bindings)?
                {
                    let scope = self
                        .sources
                        .get(&first.span)
                        .ok_or_else(|| Failure::Internal("型binderの元Sourceがない".into()))?
                        .scope
                        .clone();
                    let ty = known.ty();
                    let support = self.graph.get(domain)?.support.clone();
                    let value = self.value(
                        known,
                        Rule::Input {
                            kind: "law",
                            location: Location::Law { span: first.span },
                        },
                        vec![domain],
                        support.clone(),
                        scope,
                    )?;
                    self.finish(
                        first.span,
                        ty,
                        Some(value),
                        vec![],
                        support,
                        None,
                        None,
                        None,
                    )?
                } else if let Some((input, known)) = self.environment.iteration_argument(
                    self.graph,
                    first.span,
                    &first.name,
                    &self.bindings,
                )? {
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
                for (_index, part) in parts.iter().enumerate().skip(1) {
                    self.tick(Checkpoint::FiniteIteration)?;
                    current = self.field(
                        current,
                        &part.name,
                        (first.span.0, part.span.1),
                        parts.len() > 2,
                    )?;
                    #[cfg(test)]
                    data::observe_actual(span, self.graph.active, "field_evaluate", _index);
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
                self.field(base, &name.name, span, false)
            }
            ExprKind::Family { owner, .. } => self.owned_family(id, *owner, span, ty),
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
                    self.environment.inputs.law(),
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
                if operand
                    .reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
                {
                    return self.lexical_result(span, ty, None, vec![operand]);
                }
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
                    None if *op == UnOp::Neg => self.affine_constant(span, &ty, &[&operand])?,
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
                if !supports_binary(*op, input_ty, self.environment.inputs.law(), self.control)? {
                    return Err(self.unsupported(span, "対応済み Z/Bool 二項演算以外"));
                }
                let left = self.eval(*lhs)?;
                let right = self.eval(*rhs)?;
                let source = self.source(span, ty.clone())?;
                if source.condition_pending
                    || self
                        .environment
                        .evaluation_child_reasons(
                            self.graph,
                            source.expression,
                            &[left.evaluation, right.evaluation],
                        )?
                        .iter()
                        .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
                {
                    return self.lexical_result(span, ty, None, vec![left, right]);
                }
                let mut scope = left.scope.clone();
                scope.merge(&right.scope);
                let mut support = left.support.clone();
                support.extend(right.support.iter().cloned());
                support.sort();
                support.dedup();
                let pair = left.value.zip(right.value);
                let mut comparison = pair.filter(|_| is_comparison(*op));
                #[cfg(test)]
                let previous = data::evaluation_context(Some((span, self.graph.active)));
                let computed = partial_binary(
                    *op,
                    left.value.map(|r| self.graph.scalar(r)).transpose()?,
                    right.value.map(|r| self.graph.scalar(r)).transpose()?,
                    self.environment.inputs.law(),
                    span,
                    self.control,
                );
                #[cfg(test)]
                data::evaluation_context(previous);
                let known_value = computed?;
                let affine = if known_value.is_none() && matches!(op, BinOp::Eq | BinOp::Ne) {
                    self.affine_equality(span, input_ty, &left, &right)?
                } else {
                    None
                };
                if affine.is_some() {
                    comparison = Some((left.evaluation, right.evaluation));
                }
                let value = if let Some(value) = known_value {
                    let arguments = if is_boolean_binary(*op) {
                        vec![left.evaluation, right.evaluation]
                    } else {
                        let (l, r) = pair.ok_or_else(|| {
                            Failure::Internal("既知二項演算の左右値がない".into())
                        })?;
                        vec![l, r]
                    };
                    let evidence =
                        self.term_comparison_evidence(span, *op, &left, &right, &support, &scope)?;
                    Some(self.push(Node {
                        ty: NodeType::Value(value.ty()),
                        payload: Some(Payload::Scalar(value)),
                        rule: Rule::Input {
                            kind: "law",
                            location: Location::Law { span },
                        },
                        arguments,
                        support: support.clone(),
                        scope: scope.clone(),
                        evidence,
                        judgment: None,
                        reasons: vec![],
                    })?)
                } else if let Some((value, _)) = affine {
                    Some(value)
                } else if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
                    self.affine_constant(span, &ty, &[&left, &right])?
                } else {
                    None
                };
                let residual = if let Some((_, residual)) = affine {
                    Some(residual)
                } else if *op == BinOp::Eq && numeric::is_numeric_type(input_ty, self.control)? {
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
            ExprKind::Fn { .. }
            | ExprKind::Tuple(_)
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
        let input = spec.domain.map(|domain| self.eval(domain)).transpose()?;
        let source = self
            .sources
            .get(&spec.span)
            .ok_or_else(|| Failure::Internal("量化元Sourceがない".into()))?
            .expression;
        let mut children: Vec<_> = input.iter().cloned().collect();
        let mut evidence = Vec::new();
        let mut results = Vec::new();
        let mut scope = input
            .as_ref()
            .map(|input| input.scope.clone())
            .unwrap_or(self.graph.get(source)?.scope.clone());
        let mut domain_support = input
            .as_ref()
            .map(|input| input.support.clone())
            .unwrap_or_default();
        let mut finite = None;
        let mut owners = Vec::new();
        let mut unresolved_reasons = Vec::new();
        let members = if let Some(input) = &input {
            input
                .value
                .map(|value| -> Result<Vec<Scalar>, Failure> {
                    let (Scalar::List { items, .. } | Scalar::Set { items, .. }) =
                        self.graph.scalar(value)?
                    else {
                        return Err(Failure::Internal("量化域がList/Setでない".into()));
                    };
                    let value = data::set(spec.element.clone(), items, self.control)?;
                    let Scalar::Set { items, .. } = &value else {
                        unreachable!()
                    };
                    Ok(items.clone())
                })
                .transpose()?
        } else {
            #[cfg(test)]
            let (span, context) = (spec.span, self.graph.active);
            let enumeration = self.environment.owned_type_domain_at(
                self.graph,
                id,
                &self.bindings,
                &mut |_phase, _index| {
                    #[cfg(test)]
                    data::observe_actual(span, context, _phase, _index);
                },
            )?;
            owners = enumeration.owners;
            domain_support = enumeration.support;
            scope.merge(&enumeration.scope);
            if enumeration.values.is_none() {
                #[cfg(test)]
                data::observe_actual(spec.span, self.graph.active, "owned_type_missing", 0);
                self.tick(Checkpoint::FiniteIteration)?;
                unresolved_reasons = self.owned_type_reasons(
                    source,
                    &spec.element,
                    enumeration.type_span,
                    enumeration.missing,
                );
                self.retained_scope.merge(&scope);
            }
            enumeration.values
        };
        let member_scope = scope.clone();
        if let Some(items) = members {
            let mut elements = Vec::new();
            for item in &items {
                #[cfg(test)]
                data::observe_actual(spec.span, self.graph.active, "quant_domain", elements.len());
                self.tick(Checkpoint::FiniteIteration)?;
                elements.push(
                    self.value(
                        item.clone(),
                        Rule::Construction("domain"),
                        std::iter::once(source)
                            .chain(input.as_ref().map(|input| input.evaluation))
                            .chain(owners.iter().copied())
                            .collect(),
                        domain_support.clone(),
                        member_scope.clone(),
                    )?,
                );
                self.tick(Checkpoint::FiniteIteration)?;
            }
            let mut domain_scope = member_scope.clone();
            domain_scope.add_quantifier(spec.descriptor(None, Some(self.graph.active)));
            domain_scope.order_quantifiers_like(&self.graph.get(source)?.scope);
            let arguments = std::iter::once(source)
                .chain(input.as_ref().map(|input| input.evaluation))
                .chain(owners.iter().copied())
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
                support: domain_support.clone(),
                evidence: vec![],
                judgment: None,
                scope: domain_scope,
                reasons: vec![],
            })?;
            finite = Some(domain);
            scope.add_quantifier(spec.descriptor(finite, Some(self.graph.active)));
            scope.order_quantifiers_like(&self.graph.get(source)?.scope);
            for item in &items {
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
                    domain: input
                        .as_ref()
                        .map(|input| input.evaluation)
                        .unwrap_or(domain),
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
                        let mut counter_support = domain_support.clone();
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
        let failed = children.iter().any(|a| {
            a.reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
        });
        let mut pending = false;
        for child in &children {
            pending |= self
                .environment
                .evaluation_condition_pending(self.graph, child.evaluation)?;
        }
        let known = if finite.is_some() && !failed && !pending {
            super::quantifier::reduce(spec.kind, &results, self.control)?
        } else {
            None
        };
        let mut support = domain_support.clone();
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
            for body in &children[usize::from(input.is_some())..] {
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
        let partial_evidence = if known.is_none() {
            evidence.clone()
        } else {
            vec![]
        };
        let value = if let Some(known) = known {
            Some(
                self.push(Node {
                    ty: NodeType::Value(Type::Bool),
                    payload: Some(Payload::Scalar(Scalar::Bool(known))),
                    rule: Rule::Input {
                        kind: "law",
                        location: Location::Law { span: spec.span },
                    },
                    arguments: finite
                        .filter(|_| input.is_none())
                        .into_iter()
                        .chain(children.iter().map(|c| c.evaluation))
                        .collect(),
                    support,
                    evidence,
                    judgment: None,
                    scope,
                    reasons: vec![],
                })?,
            )
        } else {
            None
        };
        let committed_reasons = unresolved_reasons.clone();
        let result = self.finish_with_evidence(
            spec.span,
            Type::Bool,
            value,
            children,
            domain_support,
            None,
            None,
            None,
            unresolved_reasons,
            partial_evidence,
        );
        if result.is_ok() {
            self.reasons.extend(committed_reasons);
        }
        result
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
        let mut reasons = Vec::new();
        let failed = evaluated.iter().any(|a| {
            a.reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
        });
        if failed {
            return self.lexical_result(span, ty, None, evaluated);
        }
        let value = if known {
            #[cfg(test)]
            let previous = data::evaluation_context(Some((span, self.graph.active)));
            let constructed = self.environment.composite_value(id, &values);
            #[cfg(test)]
            data::evaluation_context(previous);
            if let Some(value) = constructed? {
                Some(self.value(
                    value,
                    Rule::Input {
                        kind: "law",
                        location: Location::Law { span },
                    },
                    arguments,
                    support,
                    scope,
                )?)
            } else {
                #[cfg(test)]
                data::observe_actual(span, self.graph.active, "map_condition", 0);
                self.tick(Checkpoint::FiniteIteration)?;
                let source = self
                    .sources
                    .get(&span)
                    .ok_or_else(|| Failure::Internal("Map適用の元Sourceがない".into()))?
                    .expression;
                let children: Vec<_> = evaluated.iter().map(|e| e.evaluation).collect();
                let condition = self
                    .environment
                    .map_condition(self.graph, source, &children, self.graph.nodes.len())?
                    .ok_or_else(|| {
                        Failure::Internal("値のない既知構成に反証済み条件がない".into())
                    })?;
                let edges = vec![source, children[0], children[1]];
                let actual = self.value(
                    condition.actual,
                    Rule::Construction("evaluation"),
                    edges.clone(),
                    condition.support.clone(),
                    condition.scope.clone(),
                )?;
                #[cfg(test)]
                data::observe_actual(span, self.graph.active, "map_condition", 1);
                self.tick(Checkpoint::FiniteIteration)?;
                let required = self.value(
                    condition.required,
                    Rule::Construction("domain"),
                    edges.clone(),
                    condition.support.clone(),
                    condition.scope.clone(),
                )?;
                let evidence = self.push(Node {
                    ty: NodeType::Evidence,
                    payload: Some(Payload::Counterexample {
                        bindings: condition.bindings,
                        left: actual,
                        right: required,
                        facts: condition.support.clone(),
                    }),
                    rule: Rule::Construction("evidence"),
                    arguments: edges.iter().copied().chain([actual, required]).collect(),
                    support: condition.support.clone(),
                    scope: condition.scope.clone(),
                    evidence: vec![],
                    judgment: None,
                    reasons: vec![],
                })?;
                let proposition = self.push(Node {
                    ty: NodeType::Proposition,
                    payload: Some(Payload::MapDomainCondition {
                        left: actual,
                        right: required,
                    }),
                    rule: Rule::Construction("proposition"),
                    arguments: edges
                        .into_iter()
                        .chain([actual, required, evidence])
                        .collect(),
                    support: condition.support,
                    scope: condition.scope,
                    evidence: vec![evidence],
                    judgment: Some(Judgment {
                        status: Decision::Refuted,
                        evidence: vec![evidence],
                        reasons: vec![],
                    }),
                    reasons: vec![],
                })?;
                reasons.push(Reason {
                    kind: ReasonKind::ConditionFailed {
                        condition: proposition,
                        construction: "evaluation",
                    },
                    request: self.request.id.clone(),
                    dependencies: vec![source],
                    missing: vec![],
                    location: Some(Location::Law { span }),
                });
                None
            }
        } else {
            let children: Vec<_> = evaluated.iter().collect();
            self.affine_constant(span, &ty, &children)?
        };
        self.finish_with_reasons(
            span,
            ty,
            value,
            evaluated,
            vec![],
            None,
            None,
            None,
            reasons,
        )
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
        #[cfg(test)]
        data::observe_actual(
            span,
            self.graph.active,
            "call_arguments_complete",
            arguments.len(),
        );
        let owned = self.environment.owns_call(id)?;
        let values = if owned {
            arguments
                .iter()
                .map(|a| {
                    self.environment
                        .owned_call_argument(self.graph, a.evaluation)
                })
                .collect::<Result<Vec<_>, _>>()?
        } else {
            vec![]
        };
        let mut pending = false;
        for argument in &arguments {
            pending |= self
                .environment
                .evaluation_condition_pending(self.graph, argument.evaluation)?;
        }
        let mut checks = if arguments.iter().any(|a| {
            a.reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
        }) {
            super::environment::owned_call::Checks {
                blocked: true,
                ..Default::default()
            }
        } else {
            self.environment
                .owned_call_checks_at(self.graph, declaration, &values, None, span)?
        };
        checks.blocked |= pending;
        if owned {
            #[cfg(test)]
            data::observe_actual(span, self.graph.active, "owned_call_parameter", 0);
            self.tick(Checkpoint::FiniteIteration)?;
        }
        if checks.failure.is_some() || checks.blocked {
            return self.owned_call_finish(span, ty, arguments, None, checks);
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
            instance: caller.instance,
            case: caller.case,
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
        let partial = if owned {
            Some(
                self.environment
                    .owned_call_argument(self.graph, body.evaluation)?,
            )
        } else {
            None
        };
        let checks = self.environment.owned_call_checks_at(
            self.graph,
            declaration,
            &values,
            partial.as_ref(),
            span,
        )?;
        arguments.push(body);
        if owned {
            self.owned_call_finish(span, ty, arguments, known, checks)
        } else {
            self.lexical_result(span, ty, known, arguments)
        }
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
        let source = self.source(span, ty.clone())?;
        let failed = source.condition_pending
            || self
                .environment
                .evaluation_child_reasons(
                    self.graph,
                    source.expression,
                    &children.iter().map(|c| c.evaluation).collect::<Vec<_>>(),
                )?
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }));
        let value = if let Some(known) = known.filter(|_| !failed) {
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
        chain: bool,
    ) -> Result<Evaluated, Failure> {
        let Some(reference) = base.value else {
            if self
                .environment
                .evaluation_condition_pending(self.graph, base.evaluation)?
                || base
                    .reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            {
                let source = self
                    .sources
                    .get(&span)
                    .ok_or_else(|| Failure::Internal("失敗fieldの元Sourceがない".into()))?;
                let NodeType::Expression(ty) = &self.graph.get(source.expression)?.ty else {
                    return Err(Failure::Internal("失敗fieldの元Source型がない".into()));
                };
                let ty = ty.clone();
                #[cfg(test)]
                data::observe_actual(span, self.graph.active, "failed_field", 0);
                return self.lexical_result(span, ty, None, vec![base]);
            }
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
            && !data::supported(
                &field.ty.erase(),
                self.environment.inputs.law(),
                self.control,
            )?
        {
            return Err(self.unsupported(span, "Z/Bool/Ref 以外の原始 slot 評価"));
        }
        let fact = Fact {
            snapshot,
            subject,
            field: Some(fullname),
            atom: None,
        };
        if self.environment.completion_type_supported(&field.ty)?
            && matches!(field.slot, Slot::Missing)
            && let Some(assigned) = self.environment.completion_slot(self.graph, &fact)?
        {
            let source = self
                .sources
                .get(&span)
                .ok_or_else(|| Failure::Internal("補完fieldの元Sourceがない".into()))?
                .expression;
            let analysis = self
                .environment
                .analyze_source(self.graph, span, &self.bindings)?;
            let scope = analysis
                .scalar_scope
                .ok_or_else(|| Failure::Internal("補完fieldの値Scopeがない".into()))?;
            let value = self.value(
                self.graph.scalar(assigned)?.clone(),
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                },
                vec![source, reference, assigned],
                vec![],
                scope,
            )?;
            return self.finish(
                span,
                field.ty.erase(),
                Some(value),
                vec![base],
                vec![],
                Some(fact),
                None,
                None,
            );
        }
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
                let mut arguments = vec![reference];
                if chain {
                    // chain の中間参照も、同じ slot を読む別出現の producer で
                    // 置き換えられないよう、その原出現の Source を保持する。
                    arguments.push(
                        self.sources
                            .get(&span)
                            .ok_or_else(|| Failure::Internal("chain fieldの元Sourceがない".into()))?
                            .expression,
                    );
                }
                let rule = if chain {
                    // 原出現をRuleにも固定し、Source辺を消して通常Atomの
                    // 検査経路へ移ることを防ぐ。支持は実際の終端Atomを保つ。
                    Rule::Input {
                        kind: "law",
                        location: Location::Law { span },
                    }
                } else {
                    Rule::Input {
                        kind: "atom",
                        location: Location::ArchMap {
                            pointer: pointer.clone(),
                            span: None,
                        },
                    }
                };
                let r = self.value(value, rule, arguments, vec![fact.clone()], scope)?;
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
        if self.graph.active.instance.is_none() {
            self.bind(params)?;
        }
        if self.graph.active.instance.is_some()
            && let Some(plan) =
                self.environment
                    .universal_family_plan(self.graph, self.request, &self.bindings)?
        {
            return self.universal_law_answer(plan, role);
        }
        if self.request.kind == QuestionKind::Check
            && matches!(
                self.environment.inputs.law().exprs[body].kind,
                ExprKind::Quant { .. }
            )
            && let Some(plan) =
                self.environment
                    .universal_quantifier_plan(self.graph, body, &self.bindings)?
        {
            return self.universal_law_answer(plan, role);
        }
        self.answer_regular(params, guard, body, role)
    }

    #[inline(never)]
    fn answer_regular(
        &mut self,
        params: &[Param],
        guard: Option<ExprId>,
        body: ExprId,
        role: Option<Role>,
    ) -> Result<Answer, Failure> {
        let guard_id = guard;
        let body_id = body;
        let guard = guard.map(|g| self.eval(g)).transpose()?;
        if (self.graph.active.instance.is_some() || self.graph.active.case.is_some())
            && guard
                .as_ref()
                .map(|g| self.graph.boolean(g.value))
                .transpose()?
                .flatten()
                == Some(false)
        {
            return self.inapplicable_family_row(
                params,
                guard_id.expect("guard"),
                body_id,
                role,
                guard.as_ref().expect("guard"),
            );
        }
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
        let environment =
            Environment::with_requests(prepared.inputs(), prepared.requests().requests(), control)
                .ok();
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
                instance: None,
                case: None,
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
                verified_observed: None,
                completing: false,
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
                evaluator.projection_conditions()?;
                if let Some(answer) = evaluator
                    .environment
                    .unavailable_binding_answer(evaluator.graph, request)?
                {
                    evaluator
                        .environment
                        .validate_answer(evaluator.graph, request, &answer)?;
                    evaluator.verified_observed = Some(answer.clone());
                    return Ok(answer);
                }
                if evaluator.is_family(params) {
                    evaluator.family_answer(params, guard, body, role)
                } else {
                    evaluator.answer(params, guard, body, role)
                }
            })();
            let result = if result.as_ref().is_ok_and(|answer| {
                answer
                    .reasons
                    .iter()
                    .any(|reason| matches!(reason.kind, ReasonKind::DependencyBlocked { .. }))
            }) {
                result
            } else {
                evaluator.complete_answer(result, params, guard, body, role)
            };
            // Answer の検査は意味導出の完了前に行い、post 停止で完成済み Answer を捨てない。
            let result = result.and_then(|a| {
                validate_answer(evaluator.environment, evaluator.graph, request, &a)?;
                Ok(a)
            });
            match result {
                Ok(answer) => {
                    issues.extend(answer.reasons.iter().cloned());
                    evaluator
                        .graph
                        .checked_answers
                        .push((index, answer.clone()));
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
                    let stopped = matches!(&failure, Failure::Stop(_));
                    let reason = match failure {
                        Failure::Stop(reason) => Reason::stopped(&request.id, reason),
                        Failure::Internal(operation) => {
                            internal = true;
                            Reason::internal(&request.id, operation)
                        }
                        _ => unreachable!(),
                    };
                    if stopped && let Some(mut answer) = evaluator.verified_observed.take() {
                        // 凍結したControlへ再入せず、既に検査済みのclaimとそのproducerを保持する。
                        answer.reasons.push(reason);
                        sort_reasons(&mut answer.reasons);
                        issues.extend(evaluator.reasons.iter().cloned());
                        issues.extend(answer.reasons.iter().cloned());
                        answers[index] = Some(answer);
                        continue;
                    }
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
                        && !evaluator.is_family(params)
                        && !evaluator.completing
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
        #[cfg(test)]
        instances: graph.instances,
        #[cfg(test)]
        cases: graph.cases,
        #[cfg(test)]
        universal_witnesses: graph.universal_witnesses,
        answers,
        issues,
        status,
    })
}

#[cfg(test)]
mod recheck_tests {
    use super::*;
    use crate::canonical::Json;
    mod reference_completion_tests {
        include!("reference_completion_tests.rs");
    }
    mod owner_family_completion_tests {
        include!("owner_family_completion_tests.rs");
    }
    mod finite_reference_field_tests {
        include!("finite_reference_field_tests.rs");
    }
    mod map_field_completion_tests {
        include!("map_field_completion_tests.rs");
    }
    mod identity_path_tests {
        include!("identity_path_tests.rs");
    }
    mod owned_universal_call_tests {
        include!("owned_universal_call_tests.rs");
    }
    mod dependent_owner_completion_tests {
        include!("dependent_owner_completion_tests.rs");
    }
    mod mixed_owner_answer_binding_tests {
        include!("mixed_owner_answer_binding_tests.rs");
    }
    mod free_compound_answer_binding_tests {
        include!("free_compound_answer_binding_tests.rs");
    }
    mod free_owner_answer_binding_tests {
        include!("free_owner_answer_binding_tests.rs");
    }
    mod compound_owned_binding_tests {
        include!("compound_owned_binding_tests.rs");
    }
    mod owned_binding_tests {
        include!("owned_binding_tests.rs");
    }
    mod answer_dependent_family_tests {
        include!("answer_dependent_family_tests.rs");
    }
    mod answer_family_condition_tests {
        include!("answer_family_condition_tests.rs");
    }
    mod answer_projection_condition_tests {
        include!("answer_projection_condition_tests.rs");
    }
    mod answer_projection_tests {
        include!("answer_projection_tests.rs");
    }
    mod answer_dependency_tests {
        include!("answer_dependency_tests.rs");
    }
    mod answer_binding_tests {
        include!("answer_binding_tests.rs");
    }
    include!("universal_tests.rs");
    include!("reservations_tests.rs");
    include!("dependent_family_tests.rs");
    include!("owned_family_tests.rs");
    include!("owned_type_tests.rs");
    include!("recursive_tree_tests.rs");
    include!("known_map_tests.rs");
    include!("finite_map_tests.rs");
    include!("owned_compound_tests.rs");
    include!("map_application_tests.rs");
    include!("engine_tests.rs");
    include!("term_tests.rs");
    include!("term_equality_tests.rs");
    include!("affine_term_tests.rs");
    include!("owned_call_tests.rs");
    include!("owned_compound_call_tests.rs");
    include!("owned_partial_call_tests.rs");
    mod owned_map_tests {
        include!("owned_map_call_tests.rs");
    }
    mod unknown_map_domain_tests {
        include!("unknown_map_domain_tests.rs");
    }
    mod unknown_owned_type_tests {
        include!("unknown_owned_type_tests.rs");
    }
    mod partial_container_tests {
        include!("owned_partial_container_tests.rs");
    }
    fn affine_private_fixture(body: &str) -> InputSources {
        let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Affine","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Affine.Sample","meaning":"数値を観測する対象。","parameters":[],"fields":[{"name":"z","type":"Z","meaning":"整数。"},{"name":"k","type":"Z","meaning":"別整数。"},{"name":"q","type":"Q","meaning":"有理数。"},{"name":"p","type":"Bool","meaning":"条件。"}],"alignments":[]}]}]}"#;
        let checked =
            crate::definition::check_definitions(&[("definition0", definitions.as_bytes())])
                .unwrap();
        let digest = &checked.vocabularies["Affine"].digest;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Calc {{ use vocabulary Affine version "1" digest "{digest}";
{body}
}}"#
        );
        let map = format!(
            r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Affine","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan","uri":"urn:fixture:affine","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{{"id":"base","mode":"observed","method":"数値の対象を観測する。","locations":[{{"source":"scan","path":"sample.model","span":[0,1]}}]}}],"snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Affine.Sample","origin":"base"}},{{"id":"other","type":"Affine.Sample","origin":"base"}}],"atoms":[]}},{{"id":"v2","origin":"base","subjects":[{{"id":"sample","type":"Affine.Sample","origin":"base"}}],"atoms":[]}}]}}"#
        );
        InputSources::from_bytes(
            vec![definitions.as_bytes().to_vec()],
            law.into_bytes(),
            map.into_bytes(),
        )
    }

    fn affine_private_example(body: &str, asks: &[&str]) -> ObservedEvaluation {
        let result =
            evaluate_observed_bytes(affine_private_fixture(body), asks, &mut named_call_quiet())
                .unwrap();
        assert_ne!(result.status(), "error", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        result
    }

    fn affine_private_scalars(result: &ObservedEvaluation) -> Vec<usize> {
        result
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                (matches!(
                    &node.payload,
                    Some(Payload::Scalar(Scalar::Z(_) | Scalar::Q(..)))
                ) && matches!(&node.rule, Rule::Input { kind: "law", .. })
                    && node
                        .arguments
                        .first()
                        .is_some_and(|r| matches!(result.nodes[r.0].ty, NodeType::Expression(_)))
                    && node.arguments.len() > 1)
                    .then_some(index)
            })
            .collect()
    }

    // own Source, 実左右、差Expression、残差、正規化、比較Bool。
    fn affine_comparison_chain(result: &ObservedEvaluation, normalization: usize) -> [usize; 7] {
        let node = &result.nodes[normalization];
        let Some(Payload::Normalization {
            before,
            after,
            steps,
        }) = &node.payload
        else {
            unreachable!()
        };
        let own = node.arguments[0].0;
        let left = node.arguments[1].0;
        let right = node.arguments[2].0;
        assert_eq!(before.0, node.arguments[3].0);
        assert_eq!(after.0, node.arguments[4].0);
        assert_eq!(steps.len(), 3);
        let boolean = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (index > normalization
                    && matches!(&node.payload, Some(Payload::Scalar(Scalar::Bool(_))))
                    && node.evidence == [NodeRef(normalization)])
                .then_some(index)
            })
            .unwrap();
        [own, left, right, before.0, after.0, normalization, boolean]
    }

    fn affine_comparison_proofs(result: &ObservedEvaluation) -> Vec<usize> {
        result
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                matches!(&node.payload, Some(Payload::Normalization { .. })).then_some(index)
            })
            .collect()
    }

    #[test]
    fn affine_comparison_prefixes_reject_difference_residual_normalization_and_bool_changes() {
        let result = affine_private_example(
            "view unequal(s:Sample):Bool=s.q+rat(1,2)!=s.q+rat(3,2);",
            &["value=evaluate(Calc.unequal,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        let proof = affine_comparison_proofs(&result)[0];
        let [
            own,
            left,
            right,
            difference,
            residual,
            normalization,
            boolean,
        ] = affine_comparison_chain(&result, proof);
        assert_eq!(
            data_scalar_at(&result, residual),
            &Scalar::Q((-1).into(), 1.into())
        );
        assert_eq!(data_scalar_at(&result, boolean), &Scalar::Bool(true));
        for target in [difference, residual, normalization, boolean] {
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
            assert!(result.answers[0].outputs["evaluation"].0 > target);
            assert!(!result.nodes[target].support.is_empty());
            completion_mutation(&result, target, |nodes| nodes[target].support.clear());
            completion_mutation(&result, target, |nodes| {
                nodes[target].scope.snapshots.clear()
            });
        }
        for child in [left, right] {
            assert!(matches!(
                &result.nodes[child].payload,
                Some(Payload::Evaluation { value: None, .. })
            ));
        }
        completion_mutation(&result, difference, |nodes| {
            let Some(Payload::Transform { operands, .. }) = &mut nodes[difference].payload else {
                unreachable!()
            };
            operands.swap(0, 1);
        });
        completion_mutation(&result, difference, |nodes| {
            nodes[difference].arguments.swap(1, 2)
        });
        completion_mutation(&result, difference, |nodes| {
            nodes[difference].ty = NodeType::Expression(Type::Z)
        });
        completion_mutation(&result, residual, |nodes| {
            nodes[residual].payload = Some(Payload::Scalar(Scalar::Q(0.into(), 1.into())))
        });
        completion_mutation(&result, residual, |nodes| {
            nodes[residual].payload = Some(Payload::Scalar(Scalar::Q((-2).into(), 2.into())))
        });
        completion_mutation(&result, residual, |nodes| {
            nodes[residual].arguments[0] = NodeRef(own)
        });
        for variant in 0..4 {
            completion_mutation(&result, normalization, |nodes| {
                let Some(Payload::Normalization {
                    before,
                    after,
                    steps,
                }) = &mut nodes[normalization].payload
                else {
                    unreachable!()
                };
                match variant {
                    0 => *before = NodeRef(own),
                    1 => *after = NodeRef(left),
                    2 => steps.swap(0, 1),
                    _ => {
                        steps.pop();
                    }
                }
            });
        }
        completion_mutation(&result, boolean, |nodes| {
            nodes[boolean].payload = Some(Payload::Scalar(Scalar::Bool(false)))
        });
        completion_mutation(&result, boolean, |nodes| nodes[boolean].evidence.clear());
        completion_mutation(&result, boolean, |nodes| {
            nodes[boolean].arguments[4] = NodeRef(difference)
        });
    }

    #[test]
    fn affine_comparison_rejects_other_calls_requests_and_actual_argument_producers() {
        let mut result = affine_private_example(
            "view equal(x:Z):Bool=x+1=x+1; view caller(s:Sample):Bool=equal(s.z) and equal(s.z);",
            &[
                "first=evaluate(Calc.caller,s=@v/sample)",
                "again=evaluate(Calc.caller,s=@v/sample)",
            ],
        );
        assert_eq!(result.status(), "complete");
        let proofs = affine_comparison_proofs(&result);
        assert_eq!(proofs.len(), 4);
        let prior = affine_comparison_chain(&result, proofs[0]);
        for proof in [proofs[1], proofs[2]] {
            let target = affine_comparison_chain(&result, proof);
            assert_ne!(result.contexts[prior[5]], result.contexts[target[5]]);
            assert_eq!(
                data_scalar_at(&result, prior[4]),
                data_scalar_at(&result, target[4])
            );
            for (position, target_node) in [
                (0, target[3]),
                (1, target[3]),
                (2, target[3]),
                (3, target[5]),
                (4, target[5]),
            ] {
                let replacement = NodeRef(match position {
                    0 => prior[0],
                    1 => prior[1],
                    2 => prior[2],
                    3 => prior[3],
                    _ => prior[4],
                });
                completion_mutation(&result, target_node, |nodes| {
                    nodes[target_node].arguments[position] = replacement
                });
            }
        }
        let target = affine_comparison_chain(&result, proofs[1]);
        let frame = result.contexts[target[5]].frame.unwrap();
        let prior_frame = result.contexts[prior[5]].frame.unwrap();
        let original = result.frames[frame].arguments[0];
        let foreign = result.frames[prior_frame].arguments[0];
        assert_ne!(original, foreign);
        assert_eq!(result.nodes[original.0].ty, result.nodes[foreign.0].ty);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target[6]]).unwrap();
        result.frames[frame].arguments[0] = foreign;
        rejects_named_prefix(&result, &result.nodes[..=target[6]]);
        rejects_named_prefix(&result, &result.nodes);
        result.frames[frame].arguments[0] = original;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let missing = (0..target[6])
            .find(|index| !result.nodes[*index].reasons.is_empty())
            .unwrap();
        completion_mutation(&result, target[6], |nodes| nodes[missing].reasons.clear());
    }

    #[test]
    fn affine_comparison_rejects_other_operators_sources_and_bindings_at_prefix() {
        let result = affine_private_example(
            "view eq(s:Sample):Bool=s.q+1=s.q+2; view ne(s:Sample):Bool=s.q+1!=s.q+2;",
            &[
                "eq=evaluate(Calc.eq,s=@v/sample)",
                "ne=evaluate(Calc.ne,s=@v/sample)",
            ],
        );
        assert_eq!(result.status(), "complete");
        let proofs = affine_comparison_proofs(&result);
        let prior = affine_comparison_chain(&result, proofs[0]);
        let target = affine_comparison_chain(&result, proofs[1]);
        assert_eq!(
            data_scalar_at(&result, prior[4]),
            data_scalar_at(&result, target[4])
        );
        assert_ne!(
            data_scalar_at(&result, prior[6]),
            data_scalar_at(&result, target[6])
        );
        completion_mutation(&result, target[6], |nodes| {
            nodes[target[6]].rule = result.nodes[prior[6]].rule.clone()
        });
        completion_mutation(&result, target[3], |nodes| {
            nodes[target[3]].arguments[0] = NodeRef(prior[0])
        });
        completion_mutation(&result, target[6], |nodes| {
            let Some(Payload::Expression { bindings, .. }) = &mut nodes[target[0]].payload else {
                unreachable!()
            };
            bindings[0].name.push_str("_changed");
        });
        completion_mutation(&result, target[6], |nodes| {
            let Some(Payload::Transform { bindings, .. }) = &mut nodes[target[3]].payload else {
                unreachable!()
            };
            bindings[0].ty = Type::Z;
        });
        let evaluation = result.answers[1].outputs["evaluation"].0;
        completion_mutation(&result, evaluation, |nodes| {
            let Some(Payload::Evaluation { parts, .. }) = &mut nodes[evaluation].payload else {
                unreachable!()
            };
            parts[0].residual = None;
        });
    }

    #[test]
    fn affine_comparison_finite_case_and_law_evidence_retain_original_unknown_operands() {
        let result = affine_private_example(
            "law required mixed(s:Sample):s.p and (s.z+1=s.z+2);",
            &["mixed=check(Calc.mixed,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        assert_eq!(result.answers[0].status, Decision::Refuted);
        let proofs = affine_comparison_proofs(&result);
        let cases = proofs
            .iter()
            .copied()
            .filter(|index| result.contexts[*index].case.is_some())
            .collect::<Vec<_>>();
        assert_eq!(cases.len(), 2);
        let prior = affine_comparison_chain(&result, cases[0]);
        let target = affine_comparison_chain(&result, cases[1]);
        assert_ne!(
            result.contexts[prior[5]].case,
            result.contexts[target[5]].case
        );
        assert_eq!(
            data_scalar_at(&result, prior[4]),
            data_scalar_at(&result, target[4])
        );
        completion_mutation(&result, target[3], |nodes| {
            nodes[target[3]].arguments[0] = NodeRef(prior[0])
        });
        completion_mutation(&result, target[5], |nodes| {
            nodes[target[5]].arguments[4] = NodeRef(prior[4])
        });
        let direct = affine_private_example(
            "law required no(s:Sample):s.z+1=s.z+2;",
            &["no=check(Calc.no,s=@v/sample)"],
        );
        let chain = affine_comparison_chain(&direct, affine_comparison_proofs(&direct)[0]);
        let evaluation_evidence = direct.answers[0]
            .evidence
            .iter()
            .find_map(|r| {
                matches!(
                    &direct.nodes[r.0].payload,
                    Some(Payload::EvaluationEvidence { .. })
                )
                .then_some(r.0)
            })
            .unwrap();
        let counterexample = direct.answers[0]
            .evidence
            .iter()
            .find_map(|r| {
                matches!(
                    &direct.nodes[r.0].payload,
                    Some(Payload::Counterexample { .. })
                )
                .then_some(r.0)
            })
            .unwrap();
        let Some(Payload::EvaluationEvidence {
            lhs,
            rhs,
            residual: Some(residual),
            ..
        }) = &direct.nodes[evaluation_evidence].payload
        else {
            unreachable!()
        };
        assert_eq!([lhs.0, rhs.0, residual.0], [chain[1], chain[2], chain[4]]);
        let Some(Payload::Counterexample { left, right, .. }) =
            &direct.nodes[counterexample].payload
        else {
            unreachable!()
        };
        assert_eq!([left.0, right.0], [chain[1], chain[2]]);
        for child in [*left, *right] {
            assert!(matches!(
                &direct.nodes[child.0].payload,
                Some(Payload::Evaluation { value: None, .. })
            ));
        }
        completion_mutation(&direct, evaluation_evidence, |nodes| {
            let Some(Payload::EvaluationEvidence { lhs, rhs, .. }) =
                &mut nodes[evaluation_evidence].payload
            else {
                unreachable!()
            };
            std::mem::swap(lhs, rhs);
        });
        completion_mutation(&direct, counterexample, |nodes| {
            let Some(Payload::Counterexample { left, right, .. }) =
                &mut nodes[counterexample].payload
            else {
                unreachable!()
            };
            std::mem::swap(left, right);
        });
        completion_mutation(&direct, counterexample, |nodes| {
            let Some(Payload::Counterexample { facts, .. }) = &mut nodes[counterexample].payload
            else {
                unreachable!()
            };
            facts.clear();
        });
    }

    #[test]
    fn affine_comparison_difference_coefficient_stop_preserves_source_prefix() {
        affine_comparison_phase_stop(0, 0);
    }
    #[test]
    fn affine_comparison_residual_post_stop_preserves_typed_difference_prefix() {
        affine_comparison_phase_stop(1, 1);
    }
    #[test]
    fn affine_comparison_normalization_post_stop_preserves_completed_evidence_prefix() {
        affine_comparison_phase_stop(2, 2);
    }
    #[test]
    fn affine_comparison_bool_post_stop_preserves_value_without_unfinished_parent() {
        affine_comparison_phase_stop(3, 0);
    }
    #[test]
    fn affine_comparison_verified_answer_stop_retains_current_and_prior_results() {
        affine_comparison_phase_stop(4, 0);
    }

    fn affine_comparison_phase_stop(stage: usize, kind: usize) {
        use super::super::{
            affine,
            control::{Limits, Resource, Usage},
        };
        use crate::result::Signal;
        use std::{cell::Cell, rc::Rc};
        let sources = affine_private_fixture(
            "view seed():Z=7; law required prior():1=2; view hole(s:Sample):Z=s.z; view current(s:Sample):Bool=s.q=s.q; view later():Z=19;",
        );
        let asks = [
            "seed=evaluate(Calc.seed)",
            "prior=check(Calc.prior)",
            "hole=evaluate(Calc.hole,s=@v/sample)",
            "current=evaluate(Calc.current,s=@v/sample)",
            "later=evaluate(Calc.later)",
        ];
        let normal =
            evaluate_observed_bytes(sources.clone(), &asks, &mut named_call_quiet()).unwrap();
        assert_eq!(normal.status(), "partial");
        assert_eq!(normal.answers[0].status, Decision::Established);
        assert_eq!(normal.answers[1].status, Decision::Refuted);
        assert!(!normal.answers[1].evidence.is_empty());
        assert_eq!(normal.answers[2].status, Decision::Undetermined);
        assert!(
            normal.answers[2]
                .reasons
                .iter()
                .any(|reason| matches!(reason.kind, ReasonKind::Missing))
        );
        assert_eq!(normal.answers[3].status, Decision::Established);
        assert_eq!(
            data_scalar_at(&normal, normal.answers[3].outputs["value"].0),
            &Scalar::Bool(true)
        );
        let chain = affine_comparison_chain(&normal, affine_comparison_proofs(&normal)[0]);
        for target in [chain[3], chain[4], chain[5], chain[6]] {
            rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..=target]).unwrap();
        }
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        let (limits, usage, expected) = match kind {
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
        let ready = Rc::new(Cell::new(false));
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
        let prepared = prepare_observed(sources, &asks, &mut control).unwrap();
        let (observer_arm, observer_ready) = (armed.clone(), ready.clone());
        let stopped = affine::with_observer(
            move |point| {
                if stage == 0 && observer_ready.get() && point == affine::TestPoint::Coefficient {
                    observer_arm.set(true)
                }
            },
            || {
                evaluate_observed_with_validator(
                    prepared,
                    &mut control,
                    |environment, graph, request, answer| {
                        environment.validate_answer(graph, request, answer)?;
                        if request.id == "hole" {
                            ready.set(true);
                            if (1..=3).contains(&stage) {
                                let armed = armed.clone();
                                data::observe_iterations(move |_, context, operation, index| {
                                    if context.request == 3
                                        && operation == "affine_comparison"
                                        && index == stage
                                    {
                                        armed.set(true)
                                    }
                                });
                            }
                        }
                        if request.id == "current" && stage == 4 {
                            armed.set(true)
                        }
                        Ok(())
                    },
                )
            },
        );
        data::clear_iteration_observer();
        let stopped = stopped.unwrap();
        assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
        assert_eq!(control.stop_reason(), Some(expected.clone()));
        assert_eq!(Some(probes.get()), frozen.get());
        let Json::Obj(ref normal_wire) = normal.wire() else {
            unreachable!()
        };
        let Json::Obj(ref stopped_wire) = stopped.wire() else {
            unreachable!()
        };
        let (Json::Arr(normal_answers), Json::Arr(stopped_answers)) =
            (&normal_wire["answers"], &stopped_wire["answers"])
        else {
            unreachable!()
        };
        assert_eq!(&stopped_answers[..3], &normal_answers[..3]);
        if stage == 4 {
            assert_eq!(stopped_answers[3], normal_answers[3]);
        } else {
            assert_eq!(stopped.answers[3].status, Decision::Undetermined);
            assert!(stopped.answers[3].outputs.is_empty());
            assert!(stopped.answers[3].claim.is_none());
            assert!(stopped.answers[3].evidence.is_empty());
            assert!(
                stopped.answers[3]
                    .reasons
                    .iter()
                    .any(|reason| matches!(reason.kind, ReasonKind::Missing))
            );
        }
        for answer in &stopped.answers[if stage == 4 { 4 } else { 3 }..] {
            let reason = answer
                .reasons
                .iter()
                .find(|reason| matches!(&reason.kind,ReasonKind::Stop(actual) if actual==&expected))
                .unwrap();
            let Json::Obj(ref actual) = reason.wire() else {
                unreachable!()
            };
            let Json::Obj(ref expected) = expected.wire() else {
                unreachable!()
            };
            assert_eq!(actual["details"], expected["details"]);
        }
        assert!(stopped.answers[4].outputs.is_empty());
        assert!(!stopped.contexts.iter().any(|context| context.request == 4));
        if (1..=3).contains(&stage) {
            let last = chain[stage + 3];
            assert_eq!(stopped.nodes.len(), last + 1);
            assert!(
                !stopped
                    .nodes
                    .iter()
                    .any(|node| matches!(&node.payload, Some(Payload::Normalization { .. })))
                    || stage >= 2
            );
        }
        assert!(!stopped.nodes.iter().enumerate().any(|(index, node)| {
            stopped.contexts[index].request == 3
                && matches!(
                    &node.payload,
                    Some(Payload::Counterexample { .. } | Payload::FiniteExhaustion { .. })
                )
        }));
        let (Json::Arr(normal_nodes), Json::Arr(stopped_nodes)) =
            (&normal_wire["nodes"], &stopped_wire["nodes"])
        else {
            unreachable!()
        };
        assert_eq!(stopped_nodes, &normal_nodes[..stopped_nodes.len()]);
        rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
        let before = probes.get();
        assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
        assert_eq!(probes.get(), before);
    }

    #[test]
    fn affine_normalization_recheck_reconstructs_difference_in_fresh_sessions_and_stops() {
        use super::super::{
            affine,
            control::{Limits, Usage},
        };
        use crate::result::Signal;
        use std::{cell::Cell, rc::Rc};
        let result = affine_private_example(
            "view equal(s:Sample):Bool=s.q=s.q;",
            &["equal=evaluate(Calc.equal,s=@v/sample)"],
        );
        let normalization = affine_comparison_proofs(&result)[0];
        let mut graph =
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=normalization])
                .unwrap();
        let armed = Rc::new(Cell::new(false));
        let probes = Rc::new(Cell::new(0));
        let (arm, count) = (armed.clone(), probes.clone());
        let mut control = Control::new(Limits::default(), move |point| {
            count.set(count.get() + 1);
            if arm.replace(false) {
                assert_eq!(point, Checkpoint::FiniteIteration);
                Usage {
                    signal: Some(Signal::Term),
                    ..Usage::default()
                }
            } else {
                Usage::default()
            }
        });
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        graph.active = result.contexts[normalization];
        environment
            .recheck_node(&graph, &graph.nodes[normalization], normalization)
            .unwrap();
        let before = probes.get();
        let failure = affine::with_observer(
            move |point| {
                if point == affine::TestPoint::Coefficient {
                    armed.set(true)
                }
            },
            || environment.recheck_node(&graph, &graph.nodes[normalization], normalization),
        );
        assert!(matches!(
            failure,
            Err(ValidationFailure::Stop(StopReason::Cancelled(Signal::Term)))
        ));
        assert!(probes.get() > before);
        let frozen = probes.get();
        assert!(matches!(
            environment.recheck_node(&graph, &graph.nodes[normalization], normalization),
            Err(ValidationFailure::Stop(StopReason::Cancelled(Signal::Term)))
        ));
        assert_eq!(probes.get(), frozen);
        assert_eq!(
            control.checkpoint(Checkpoint::Expression),
            Err(StopReason::Cancelled(Signal::Term))
        );
        assert_eq!(probes.get(), frozen);
        rebuild_for_origin_and_support_recheck(&result, &graph.nodes).unwrap();
    }

    #[test]
    fn affine_constants_recheck_scalar_prefix_values_types_sources_and_children() {
        let result = affine_private_example(
            r#"view z(s:Sample):Z=s.z-s.z;
view q(s:Sample):Q=((s.q+rat(1,2))+rat(1,2))-s.q;
view foreign(s:Sample):Z=s.z-s.z;"#,
            &[
                "z=evaluate(Calc.z,s=@v/sample)",
                "q=evaluate(Calc.q,s=@v/sample)",
                "other=evaluate(Calc.foreign,s=@v/sample)",
            ],
        );
        assert_eq!(result.status(), "complete");
        let scalars = affine_private_scalars(&result);
        assert_eq!(scalars.len(), 3);
        for &target in &scalars[..2] {
            let node = &result.nodes[target];
            let graph =
                rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
            assert!(matches!(&node.ty, NodeType::Value(Type::Z | Type::Q)));
            let expected = if node.ty == NodeType::Value(Type::Z) {
                Scalar::Z(0.into())
            } else {
                Scalar::Q(1.into(), 1.into())
            };
            assert_eq!(graph.scalar(NodeRef(target)).unwrap(), &expected);
            assert_eq!(node.arguments.len(), 3);
            assert!(node.arguments.iter().all(|r| r.0 < target));
            assert!(!node.support.is_empty());
            assert!(result.nodes[target+1..].iter().any(|parent| matches!(&parent.payload, Some(Payload::Evaluation { value: Some(v), .. }) if v.0 == target)));
            for variant in 0..7 {
                completion_mutation(&result, target, |nodes| match variant {
                    0 => nodes[target].payload = Some(Payload::Scalar(Scalar::Z(9.into()))),
                    1 => nodes[target].ty = NodeType::Value(Type::Bool),
                    2 => nodes[target].arguments.swap(1, 2),
                    3 => {
                        nodes[target].arguments.remove(0);
                    }
                    4 => nodes[target].support.clear(),
                    5 => nodes[target].scope.snapshots.clear(),
                    _ => nodes[target].arguments[0] = node.arguments[1],
                });
            }
            if let Scalar::Q(..) = graph.scalar(NodeRef(target)).unwrap() {
                completion_mutation(&result, target, |nodes| {
                    nodes[target].payload = Some(Payload::Scalar(Scalar::Q(2.into(), 2.into())))
                });
                completion_mutation(&result, target, |nodes| {
                    nodes[target].payload =
                        Some(Payload::Scalar(Scalar::Q((-1).into(), (-1).into())))
                });
            }
        }
        let target = scalars[2];
        let own_source = result.nodes[target].arguments[0];
        let foreign_source = result.nodes[scalars[0]].arguments[0];
        assert_ne!(own_source, foreign_source);
        completion_mutation(&result, target, |nodes| {
            nodes[target].arguments[0] = foreign_source
        });
        completion_mutation(&result, target, |nodes| {
            let Rule::Input { location, .. } = &mut nodes[target].rule else {
                unreachable!()
            };
            let Some(Payload::Expression {
                location: original, ..
            }) = &result.nodes[foreign_source.0].payload
            else {
                unreachable!()
            };
            *location = original.clone();
        });
    }

    #[test]
    fn affine_constants_recheck_exact_call_request_subject_and_snapshot_producers() {
        let mut result = affine_private_example(
            "view shrink(x:Q):Q=x-x; view caller(s:Sample):Q=shrink(s.q)+shrink(s.q); view slot(s:Sample):Q=s.q-s.q;",
            &[
                "first=evaluate(Calc.caller,s=@v/sample)",
                "again=evaluate(Calc.caller,s=@v/sample)",
                "other=evaluate(Calc.slot,s=@v/other)",
                "snapshot=evaluate(Calc.slot,s=@v2/sample)",
            ],
        );
        assert_eq!(result.status(), "complete");
        let scalars = affine_private_scalars(&result);
        assert_eq!(scalars.len(), 6);
        for pair in scalars.windows(2) {
            let (prior, target) = (pair[0], pair[1]);
            assert_eq!(result.nodes[prior].ty, result.nodes[target].ty);
            assert_eq!(
                data_scalar_at(&result, prior),
                data_scalar_at(&result, target)
            );
            assert_ne!(result.contexts[prior], result.contexts[target]);
            for index in 0..3 {
                let old = result.nodes[prior].arguments[index];
                assert_ne!(old, result.nodes[target].arguments[index]);
                completion_mutation(&result, target, |nodes| {
                    nodes[target].arguments[index] = old
                });
            }
        }
        let target = scalars[1];
        let context = result.contexts[target];
        let frame = context.frame.unwrap();
        let previous = result.contexts[scalars[0]].frame.unwrap();
        let original = result.frames[frame].arguments[0];
        let foreign = result.frames[previous].arguments[0];
        assert_ne!(original, foreign);
        assert_eq!(result.nodes[original.0].ty, result.nodes[foreign.0].ty);
        assert!(matches!(
            &result.nodes[original.0].payload,
            Some(Payload::Evaluation { value: None, .. })
        ));
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
        result.frames[frame].arguments[0] = foreign;
        rejects_named_prefix(&result, &result.nodes[..=target]);
        rejects_named_prefix(&result, &result.nodes);
        result.frames[frame].arguments[0] = original;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        // 独立sessionは成功memoを持ち越さず、元欠測理由の省略を照合する。
        let field = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (index < scalars[0]
                    && !node.reasons.is_empty()
                    && matches!(&node.payload, Some(Payload::Evaluation { value: None, .. })))
                .then_some(index)
            })
            .unwrap();
        completion_mutation(&result, target, |nodes| nodes[field].reasons.clear());
        let target = scalars[4];
        let source = result.nodes[target].arguments[0].0;
        completion_mutation(&result, target, |nodes| {
            let Some(Payload::Expression { bindings, .. }) = &mut nodes[source].payload else {
                unreachable!()
            };
            assert!(!bindings.is_empty());
            bindings[0].name.push_str("_changed");
        });
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }

    #[test]
    fn affine_constants_recheck_comparison_residual_counterexample_and_missing_origin() {
        let result = affine_private_example(
            "view hole(s:Sample):Z=s.z; law required yes(s:Sample):s.z-s.z=0; law required no(s:Sample):s.z-s.z=1;",
            &[
                "hole=evaluate(Calc.hole,s=@v/sample)",
                "yes=check(Calc.yes,s=@v/sample)",
                "no=check(Calc.no,s=@v/sample)",
            ],
        );
        assert_eq!(result.status(), "partial");
        assert_eq!(result.answers[0].status, Decision::Undetermined);
        assert!(!result.answers[0].outputs.contains_key("value"));
        assert_eq!(result.answers[1].status, Decision::Established);
        assert_eq!(result.answers[2].status, Decision::Refuted);
        for answer in &result.answers[1..] {
            assert!(
                answer
                    .reasons
                    .iter()
                    .any(|reason| matches!(reason.kind, ReasonKind::Missing))
            );
            assert!(!answer.evidence.is_empty());
            let scalar = result
                .nodes
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    (result.contexts[index].request == if answer.id == "yes" { 1 } else { 2 }
                        && matches!(&node.rule, Rule::Input { kind: "law", .. })
                        && matches!(&node.payload, Some(Payload::Scalar(Scalar::Bool(_)))))
                    .then_some(index)
                })
                .unwrap();
            completion_mutation(&result, scalar, |nodes| {
                nodes[scalar].payload = Some(Payload::Scalar(Scalar::Bool(answer.id != "yes")))
            });
        }
        let residual = result.nodes.iter().enumerate().find_map(|(index,node)| {
            (result.contexts[index].request == 2 && matches!(&node.rule, Rule::Construction("evaluation")) && matches!(&node.payload, Some(Payload::Scalar(Scalar::Z(value))) if *value == (-1).into())).then_some(index)
        }).unwrap();
        completion_mutation(&result, residual, |nodes| {
            nodes[residual].payload = Some(Payload::Scalar(Scalar::Z(0.into())))
        });
        let counterexample = result.answers[2]
            .evidence
            .iter()
            .find_map(|r| {
                matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::Counterexample { .. })
                )
                .then_some(r.0)
            })
            .unwrap();
        let Some(Payload::Counterexample {
            left, right, facts, ..
        }) = &result.nodes[counterexample].payload
        else {
            unreachable!()
        };
        assert_eq!(data_scalar_at(&result, left.0), &Scalar::Z(0.into()));
        assert_eq!(data_scalar_at(&result, right.0), &Scalar::Z(1.into()));
        assert_eq!(
            facts,
            &[Fact {
                snapshot: "v".into(),
                subject: "sample".into(),
                field: None,
                atom: None,
            }]
        );
        assert!(result.answers[2].reasons.iter().any(|reason| {
            matches!(reason.kind, ReasonKind::Missing)
                && reason.missing.contains(&Fact {
                    snapshot: "v".into(),
                    subject: "sample".into(),
                    field: Some("Affine.Sample.z".into()),
                    atom: None,
                })
        }));
        completion_mutation(&result, counterexample, |nodes| {
            let Some(Payload::Counterexample { facts, .. }) = &mut nodes[counterexample].payload
            else {
                unreachable!()
            };
            facts.clear();
        });
        completion_mutation(&result, counterexample, |nodes| {
            let Some(Payload::Counterexample { left, right, .. }) =
                &mut nodes[counterexample].payload
            else {
                unreachable!()
            };
            std::mem::swap(left, right);
        });
    }

    #[test]
    fn affine_constants_in_finite_cases_recheck_whole_and_foreign_case_producers() {
        let result = affine_private_example(
            "view mixed(s:Sample):Bool=(s.p and (s.q-s.q=rat(0,1))) or not s.p;",
            &["mixed=evaluate(Calc.mixed,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        assert_eq!(
            data_scalar_at(&result, result.answers[0].outputs["value"].0),
            &Scalar::Bool(true)
        );
        let scalars = affine_private_scalars(&result);
        let cases = scalars
            .iter()
            .copied()
            .filter(|index| result.contexts[*index].case.is_some())
            .collect::<Vec<_>>();
        assert_eq!(cases.len(), 2);
        let (prior, target) = (cases[0], cases[1]);
        assert_ne!(result.contexts[prior].case, result.contexts[target].case);
        assert_eq!(
            data_scalar_at(&result, prior),
            data_scalar_at(&result, target)
        );
        for index in 0..3 {
            completion_mutation(&result, target, |nodes| {
                nodes[target].arguments[index] = result.nodes[prior].arguments[index]
            });
        }
        assert!(result.cases.iter().all(|case| case.values.len() == 1));
        assert!(
            result
                .nodes
                .iter()
                .filter(|node| matches!(
                    &node.payload,
                    Some(Payload::Scalar(Scalar::Z(_) | Scalar::Q(..)))
                ))
                .all(|node| !matches!(&node.rule, Rule::Construction("completion_assignment")))
        );
        let whole = result.answers[0].outputs["evaluation"].0;
        completion_mutation(&result, whole, |nodes| {
            let Some(Payload::Evaluation { parts, .. }) = &mut nodes[whole].payload else {
                unreachable!()
            };
            assert!(!parts[0].children.is_empty());
            parts[0].children.pop();
        });
    }

    #[test]
    fn affine_coefficient_stop_preserves_prior_results_and_source_prefix() {
        affine_private_phase_stop("coefficient", 0);
    }
    #[test]
    fn affine_constant_stop_preserves_prior_results_and_source_prefix() {
        affine_private_phase_stop("constant", 1);
    }
    #[test]
    fn affine_scalar_post_stop_preserves_completed_scalar_prefix() {
        affine_private_phase_stop("scalar", 2);
    }
    #[test]
    fn affine_verified_current_post_stop_retains_value_and_unstarted_request() {
        affine_private_phase_stop("verified", 0);
    }

    fn affine_private_phase_stop(phase: &'static str, kind: usize) {
        use super::super::{
            affine,
            control::{Limits, Resource, Usage},
        };
        use crate::result::Signal;
        use std::{cell::Cell, rc::Rc};
        let sources = affine_private_fixture(
            "view seed():Z=7; law required prior():1=2; view hole(s:Sample):Z=s.z; view current(s:Sample):Q=s.q-s.q; view later():Z=19;",
        );
        let asks = [
            "seed=evaluate(Calc.seed)",
            "prior=check(Calc.prior)",
            "hole=evaluate(Calc.hole,s=@v/sample)",
            "current=evaluate(Calc.current,s=@v/sample)",
            "later=evaluate(Calc.later)",
        ];
        let normal =
            evaluate_observed_bytes(sources.clone(), &asks, &mut named_call_quiet()).unwrap();
        assert_eq!(normal.status(), "partial");
        assert_eq!(normal.answers[0].status, Decision::Established);
        assert_eq!(normal.answers[1].status, Decision::Refuted);
        assert_eq!(normal.answers[2].status, Decision::Undetermined);
        assert_eq!(normal.answers[3].status, Decision::Established);
        assert_eq!(
            data_scalar_at(&normal, normal.answers[3].outputs["value"].0),
            &Scalar::Q(0.into(), 1.into())
        );
        assert!(!normal.answers[1].evidence.is_empty());
        assert!(
            normal.answers[2]
                .reasons
                .iter()
                .any(|reason| matches!(reason.kind, ReasonKind::Missing))
        );
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        let (limits, usage, expected) = match kind {
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
        let ready = Rc::new(Cell::new(false));
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
        let prepared = prepare_observed(sources, &asks, &mut control).unwrap();
        let (observer_arm, observer_ready) = (armed.clone(), ready.clone());
        let stopped = affine::with_observer(
            move |point| {
                if observer_ready.get()
                    && ((phase == "coefficient" && point == affine::TestPoint::Coefficient)
                        || (phase == "constant" && point == affine::TestPoint::Constant))
                {
                    observer_arm.set(true);
                }
            },
            || {
                evaluate_observed_with_validator(
                    prepared,
                    &mut control,
                    |environment, graph, request, answer| {
                        environment.validate_answer(graph, request, answer)?;
                        if request.id == "hole" {
                            ready.set(true);
                            if phase == "scalar" {
                                let armed = armed.clone();
                                data::observe_iterations(move |_, context, operation, index| {
                                    if context.request == 3
                                        && operation == "affine_scalar"
                                        && index == 1
                                    {
                                        armed.set(true)
                                    }
                                });
                            }
                        }
                        if request.id == "current" && phase == "verified" {
                            armed.set(true)
                        }
                        Ok(())
                    },
                )
            },
        );
        data::clear_iteration_observer();
        let stopped = stopped.unwrap();
        assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
        assert_eq!(control.stop_reason(), Some(expected.clone()));
        assert_eq!(Some(probes.get()), frozen.get());
        let Json::Obj(ref normal_wire) = normal.wire() else {
            unreachable!()
        };
        let Json::Obj(ref stopped_wire) = stopped.wire() else {
            unreachable!()
        };
        let (Json::Arr(normal_answers), Json::Arr(stopped_answers)) =
            (&normal_wire["answers"], &stopped_wire["answers"])
        else {
            unreachable!()
        };
        assert_eq!(&stopped_answers[..3], &normal_answers[..3]);
        if phase == "verified" {
            assert_eq!(stopped_answers[3], normal_answers[3]);
        } else {
            assert_eq!(stopped.answers[3].status, Decision::Undetermined);
            assert!(stopped.answers[3].outputs.is_empty());
            assert!(stopped.answers[3].evidence.is_empty());
            assert!(stopped.answers[3].claim.is_none());
            assert!(
                stopped.answers[3]
                    .reasons
                    .iter()
                    .any(|reason| matches!(reason.kind, ReasonKind::Missing))
            );
        }
        let first_unfinished = if phase == "verified" { 4 } else { 3 };
        for answer in &stopped.answers[first_unfinished..] {
            let reason = answer
                .reasons
                .iter()
                .find(|reason| matches!(&reason.kind,ReasonKind::Stop(actual) if actual==&expected))
                .unwrap();
            let Json::Obj(ref reason_wire) = reason.wire() else {
                unreachable!()
            };
            let Json::Obj(ref expected_wire) = expected.wire() else {
                unreachable!()
            };
            assert_eq!(reason_wire["details"], expected_wire["details"]);
        }
        assert_eq!(stopped.answers[4].status, Decision::Undetermined);
        assert!(stopped.answers[4].outputs.is_empty());
        assert!(!stopped.contexts.iter().any(|context| context.request == 4));
        let scalars = affine_private_scalars(&stopped);
        if phase == "scalar" {
            assert_eq!(scalars.len(), 1);
            assert_eq!(scalars[0] + 1, stopped.nodes.len());
            assert_eq!(
                data_scalar_at(&stopped, scalars[0]),
                &Scalar::Q(0.into(), 1.into())
            );
        } else if phase != "verified" {
            assert!(scalars.is_empty())
        }
        assert!(!stopped.nodes.iter().enumerate().any(|(index, node)| {
            stopped.contexts[index].request == 3
                && matches!(
                    &node.payload,
                    Some(Payload::Counterexample { .. } | Payload::FiniteExhaustion { .. })
                )
        }));
        let (Json::Arr(normal_nodes), Json::Arr(stopped_nodes)) =
            (&normal_wire["nodes"], &stopped_wire["nodes"])
        else {
            unreachable!()
        };
        assert_eq!(stopped_nodes, &normal_nodes[..stopped_nodes.len()]);
        rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
        let before = probes.get();
        assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
        assert_eq!(probes.get(), before);
    }

    #[test]
    fn affine_scalar_recheck_stop_does_not_reuse_success_memo_or_probe_after_stop() {
        use super::super::{
            affine,
            control::{Limits, Usage},
        };
        use crate::result::Signal;
        use std::{cell::Cell, rc::Rc};
        let result = affine_private_example(
            "view q(s:Sample):Q=s.q-s.q;",
            &["q=evaluate(Calc.q,s=@v/sample)"],
        );
        let scalar = affine_private_scalars(&result)[0];
        let mut graph =
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
        let armed = Rc::new(Cell::new(false));
        let probes = Rc::new(Cell::new(0));
        let (arm, count) = (armed.clone(), probes.clone());
        let mut control = Control::new(Limits::default(), move |point| {
            count.set(count.get() + 1);
            if arm.replace(false) {
                assert_eq!(point, Checkpoint::FiniteIteration);
                Usage {
                    signal: Some(Signal::Term),
                    ..Usage::default()
                }
            } else {
                Usage::default()
            }
        });
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        graph.active = result.contexts[scalar];
        environment
            .recheck_node(&graph, &graph.nodes[scalar], scalar)
            .unwrap();
        let before = probes.get();
        let failure = affine::with_observer(
            move |point| {
                if point == affine::TestPoint::Constant {
                    armed.set(true)
                }
            },
            || environment.recheck_node(&graph, &graph.nodes[scalar], scalar),
        );
        assert!(matches!(
            failure,
            Err(ValidationFailure::Stop(StopReason::Cancelled(Signal::Term)))
        ));
        assert!(probes.get() > before);
        let frozen = probes.get();
        assert!(matches!(
            environment.recheck_node(&graph, &graph.nodes[scalar], scalar),
            Err(ValidationFailure::Stop(StopReason::Cancelled(Signal::Term)))
        ));
        assert_eq!(probes.get(), frozen);
        assert_eq!(
            control.checkpoint(Checkpoint::Expression),
            Err(StopReason::Cancelled(Signal::Term))
        );
        assert_eq!(probes.get(), frozen);
        rebuild_for_origin_and_support_recheck(&result, &graph.nodes).unwrap();
    }

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
            graph.requests = result.prepared.requests().requests().to_vec();
            graph.contexts = result.contexts.clone();
            graph.frames = result.frames.clone();
            graph.iterations = result.iterations.clone();
            graph.instances = result.instances.clone();
            graph.cases = result.cases.clone();
            graph.universal_witnesses = result.universal_witnesses.clone();
            let evaluation = result.answers[4].outputs["evaluation"];
            graph.active = result.contexts[evaluation.0];
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
        let environment = Environment::with_requests(
            result.prepared.inputs(),
            result.prepared.requests().requests(),
            &mut control,
        )
        .map_err(ValidationFailure::from)?;
        let mut graph = Graph::new(&control);
        graph.requests = result.prepared.requests().requests().to_vec();
        graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
        graph.frames = result.frames.clone();
        graph.iterations = result.iterations.clone();
        graph.instances = result.instances.clone();
        graph.cases = result.cases.clone();
        graph.universal_witnesses = result.universal_witnesses.clone();
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
        let Signature::Law { body, .. } =
            &result.prepared.inputs().law().declarations["R.condition"].signature
        else {
            unreachable!()
        };
        let body_span = result.prepared.inputs().law().exprs[*body].span;
        let original:Vec<_>=result.nodes.iter().enumerate().filter_map(|(index,node)| {
            let context=result.contexts[index];
            if context.request!=answer_index || context.case.is_some() || context.frame.is_some() || context.instance.is_some() || context.iteration.is_some() {return None;}
            if !matches!(&node.payload,Some(Payload::Evaluation {..})) {return None;}
            let instance=*node.arguments.first()?;
            (matches!(&result.nodes[instance.0].payload,Some(Payload::LawInstance {name,body,..}) if name=="R.condition" && matches!(&result.nodes[body.0].payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==body_span))).then_some(NodeRef(index))
        }).collect();
        assert_eq!(original.len(), 1, "unique observed conditional application");
        let root = original[0];
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=root.0]).unwrap();
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
        assert_eq!(
            graph.scalar(answer.outputs["value"]).unwrap(),
            &Scalar::Bool(false)
        );
        let operation = original_view_evaluation_for_answer(&result, "and_value");
        let Some(Payload::Evaluation {
            value: Some(value), ..
        }) = &result.nodes[operation.0].payload
        else {
            panic!("known observed native conjunction")
        };
        let value = *value;
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
        let prior_or = original_view_evaluation_for_answer(&result, "or_value");
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

    #[test]
    fn finite_law_parameter_family_rechecks_normal_scalar_prefix_and_source() {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(&[], "law required every(b: Bool): b or not b;"),
            &["family=check(Calc.every)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert_eq!(result.answers[0].status, Decision::Established);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let evaluation = result.answers[0].outputs["evaluation"];
        let Some(Payload::Evaluation {
            value: Some(value), ..
        }) = &result.nodes[evaluation.0].payload
        else {
            panic!("whole value")
        };
        assert!(value.0 < evaluation.0);
        let prefix = &result.nodes[..=value.0];
        rebuild_for_origin_and_support_recheck(&result, prefix).unwrap();
        let mut changed = prefix.to_vec();
        let source=changed.iter().position(|n| matches!(&n.payload,Some(Payload::Expression {parameters,..}) if !parameters.is_empty())).unwrap();
        let Some(Payload::Expression { parameters, .. }) = &mut changed[source].payload else {
            unreachable!()
        };
        parameters[0].0 = "other".into();
        rejects_named_prefix(&result, &changed);
    }

    fn finite_family_example(body: &str, asks: &[&str], missing: bool) -> ObservedEvaluation {
        evaluate_observed_bytes(
            numeric_recheck_fixture(if missing { &["p"] } else { &[] }, body),
            asks,
            &mut named_call_quiet(),
        )
        .unwrap()
    }
    fn family_whole(result: &ObservedEvaluation, request: usize) -> (usize, usize, Vec<NodeRef>) {
        let evaluation = result.answers[request].outputs["evaluation"].0;
        let Some(Payload::Evaluation { parts, .. }) = &result.nodes[evaluation].payload else {
            panic!("whole Evaluation")
        };
        (
            result.nodes[evaluation].arguments[0].0,
            result.nodes[evaluation].arguments[1].0,
            parts[0].children.clone(),
        )
    }
    #[test]
    fn finite_law_non_applicable_rows_reject_foreign_and_unrelated_producers() {
        let result = finite_family_example(
            "law required skipped(b:Bool) when false and true:false;",
            &["family=check(Calc.skipped)"],
            false,
        );
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert_eq!(result.answers[0].status, Decision::Established);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let (_, _, rows) = family_whole(&result, 0);
        assert_eq!(rows.len(), 2);
        let first = rows[0];
        let row = rows[1];
        let Some(Payload::Evaluation {
            value: Some(foreign_value),
            applicability: "not_applicable",
            ..
        }) = &result.nodes[first.0].payload
        else {
            panic!("first NA applied Evaluation")
        };
        let Some(Payload::Evaluation {
            value: Some(own_value),
            applicability: "not_applicable",
            parts,
            ..
        }) = &result.nodes[row.0].payload
        else {
            panic!("second NA applied Evaluation")
        };
        assert!(parts[1].value.is_none() && parts[1].children.is_empty());
        assert_ne!(own_value, foreign_value);
        assert_ne!(
            result.contexts[row.0].instance,
            result.contexts[foreign_value.0].instance
        );
        let instance = result.nodes[row.0].arguments[0];
        let guard = result.nodes[row.0].arguments[1];
        assert_eq!(parts[0].children, vec![guard]);
        let Some(Payload::Evaluation {
            value: Some(guard_value),
            parts: guard_parts,
            ..
        }) = &result.nodes[guard.0].payload
        else {
            panic!("real false guard")
        };
        assert!(matches!(
            result.nodes[guard_value.0].payload,
            Some(Payload::Scalar(Scalar::Bool(false)))
        ));
        assert_eq!(guard_parts[0].children.len(), 2);
        let left = guard_parts[0].children[0];
        let right = guard_parts[0].children[1];
        let Some(Payload::Evaluation {
            expression: left_source,
            value: Some(left_value),
            ..
        }) = &result.nodes[left.0].payload
        else {
            panic!("left literal")
        };
        let Some(Payload::Evaluation {
            expression: right_source,
            value: Some(unrelated_true),
            ..
        }) = &result.nodes[right.0].payload
        else {
            panic!("right literal")
        };
        assert!(matches!(
            result.nodes[left_value.0].payload,
            Some(Payload::Scalar(Scalar::Bool(false)))
        ));
        for reference in [*foreign_value, *own_value, *unrelated_true] {
            assert!(matches!(
                result.nodes[reference.0].payload,
                Some(Payload::Scalar(Scalar::Bool(true)))
            ));
        }
        assert_ne!(own_value, unrelated_true);
        assert_eq!(result.contexts[right.0], result.contexts[row.0]);
        assert_eq!(result.contexts[unrelated_true.0], result.contexts[row.0]);
        // 実二項評価は元ASTの左右を順に生成し、falseでも右のtrueを読む。
        for (reference, expected) in [
            (*left_source, b"false".as_slice()),
            (*right_source, b"true".as_slice()),
        ] {
            let Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) = &result.nodes[reference.0].payload
            else {
                panic!("literal Source")
            };
            assert_eq!(
                &result.prepared.inputs().sources().law().bytes()[span.0..span.1],
                expected
            );
        }
        assert!(
            left.0 < right.0 && right.0 < guard.0 && guard.0 < instance.0 && instance.0 < row.0
        );
        let proposition = result.nodes.iter().enumerate().find_map(|(index,node)| {
            (matches!(&node.payload,Some(Payload::Proposition {instance:actual}) if *actual==instance)
                && node.arguments==[instance,row]).then_some(index)
        }).unwrap();
        assert!(row.0 < proposition);
        let mut failures = Vec::new();
        for (label, target, replacement, replace_value) in [
            (
                "foreign-instance NA true Scalar",
                row.0,
                *foreign_value,
                true,
            ),
            (
                "same-row unrelated true guard-child Scalar",
                row.0,
                *unrelated_true,
                true,
            ),
            (
                "NA Proposition to false guard Evaluation",
                proposition,
                guard,
                false,
            ),
            (
                "NA Proposition to true raw child Evaluation",
                proposition,
                right,
                false,
            ),
        ] {
            let prefix = &result.nodes[..=target];
            rebuild_for_origin_and_support_recheck(&result, prefix).unwrap();
            for (extent, original) in [("prefix", prefix), ("full", result.nodes.as_slice())] {
                let mut changed = original.to_vec();
                if replace_value {
                    let Some(Payload::Evaluation { value, .. }) = &mut changed[target].payload
                    else {
                        unreachable!()
                    };
                    assert_ne!(*value, Some(replacement));
                    *value = Some(replacement);
                } else {
                    assert_ne!(changed[target].arguments[1], replacement);
                    changed[target].arguments[1] = replacement;
                }
                let outcome = rebuild_for_origin_and_support_recheck(&result, &changed);
                match outcome {
                    Err(ValidationFailure::Internal(_)) => {}
                    Err(other) => failures.push(format!("{label} ({extent}): {other:?}")),
                    Ok(_) => failures.push(format!("{label} ({extent}): accepted")),
                }
            }
        }
        assert!(
            failures.is_empty(),
            "all NA consumer substitution outcomes:\n{}",
            failures.join("\n")
        );
    }

    #[test]
    fn finite_law_families_recheck_products_rows_guards_and_coverage() {
        let result = finite_family_example(
            "law required product(a: Bool,b: Bool): a or not a; law required guarded(b: Bool,s: Sample) when b: s.p; law required skipped(b: Bool,s: Sample) when false: s.p;",
            &[
                "product=check(Calc.product)",
                "guarded=check(Calc.guarded,s=@v/sample)",
                "skipped=check(Calc.skipped,s=@v/sample)",
            ],
            false,
        );
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let (template, domain, rows) = family_whole(&result, 0);
        assert_eq!(rows.len(), 4);
        let Some(Payload::Domain { elements, ty }) = &result.nodes[domain].payload else {
            panic!("product Domain")
        };
        assert_eq!(ty, &Type::Tuple(vec![Type::Bool, Type::Bool]));
        assert_eq!(elements.len(), 4);
        let Some(Payload::Evaluation {
            value: Some(scalar),
            ..
        }) = &result.nodes[result.answers[0].outputs["evaluation"].0].payload
        else {
            panic!("whole Scalar")
        };
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar.0]).unwrap();
        for variant in 0..9 {
            let mut changed = result.nodes.clone();
            match variant {
                0 => {
                    let Some(Payload::Domain { ty, .. }) = &mut changed[domain].payload else {
                        unreachable!()
                    };
                    *ty = Type::Tuple(vec![Type::Bool, Type::Unit]);
                }
                1 | 2 => {
                    let Some(Payload::Domain { elements, .. }) = &mut changed[domain].payload
                    else {
                        unreachable!()
                    };
                    if variant == 1 {
                        elements.pop();
                        changed[domain].arguments.pop();
                    } else {
                        elements[1] = elements[0];
                        let len = changed[domain].arguments.len();
                        changed[domain].arguments[len - 3] = changed[domain].arguments[len - 4];
                    }
                }
                3 => {
                    let n = changed[template].arguments.len();
                    changed[template].arguments[n - 1] = changed[template].arguments[n - 2];
                }
                4 => {
                    changed[template].arguments.pop();
                }
                5 => {
                    let source = changed[domain].arguments[0].0;
                    let Some(Payload::Expression { parameters, .. }) = &mut changed[source].payload
                    else {
                        unreachable!()
                    };
                    parameters.swap(0, 1);
                }
                6 => {
                    changed[domain].scope.quantifiers.swap(0, 1);
                }
                7 => {
                    let proof = result.answers[0]
                        .evidence
                        .iter()
                        .find(|r| {
                            matches!(
                                result.nodes[r.0].payload,
                                Some(Payload::FiniteExhaustion { .. })
                            )
                        })
                        .unwrap()
                        .0;
                    let Some(Payload::FiniteExhaustion { checked, .. }) =
                        &mut changed[proof].payload
                    else {
                        unreachable!()
                    };
                    *checked -= 1;
                }
                _ => {
                    let instance = changed[template].arguments[2].0;
                    let other = changed[template].arguments[3].0;
                    let Some(Payload::LawInstance { bindings: b, .. }) = &changed[other].payload
                    else {
                        unreachable!()
                    };
                    let foreign = b[0].value;
                    let Some(Payload::LawInstance { bindings, .. }) =
                        &mut changed[instance].payload
                    else {
                        unreachable!()
                    };
                    bindings[0].value = foreign;
                    let n = changed[instance].arguments.len();
                    changed[instance].arguments[n - 2] = foreign;
                }
            }
            assert!(
                matches!(
                    rebuild_for_origin_and_support_recheck(&result, &changed),
                    Err(ValidationFailure::Internal(_))
                ),
                "product variant {variant}"
            );
        }
        let mut reordered = result.nodes.clone();
        let Some(Payload::Domain { elements, .. }) = &mut reordered[domain].payload else {
            unreachable!()
        };
        elements.reverse();
        reordered[domain].arguments[3..].reverse();
        // 実row/実LawInstanceとproofの集合表示は順を変えても同じcoverageを主張する。
        reordered[template].arguments[2..6].reverse();
        reordered[template].arguments[6..].reverse();
        let evaluation = result.answers[0].outputs["evaluation"].0;
        let Some(Payload::Evaluation { parts, .. }) = &mut reordered[evaluation].payload else {
            unreachable!()
        };
        parts[0].children.reverse();
        reordered[evaluation].arguments[2..].reverse();
        for &proof in &result.answers[0].evidence {
            if let Some(Payload::FiniteExhaustion { instances, .. }) =
                &mut reordered[proof.0].payload
            {
                instances.reverse();
            }
        }
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        assert_eq!(result.answers[1].status, Decision::Refuted);
        assert_eq!(result.answers[2].status, Decision::Established);
        let (_, _, skiprows) = family_whole(&result, 2);
        assert_eq!(skiprows.len(), 2);
        for row in skiprows {
            let Some(Payload::Evaluation {
                applicability,
                parts,
                ..
            }) = &result.nodes[row.0].payload
            else {
                unreachable!()
            };
            assert_eq!(*applicability, "not_applicable");
            assert!(parts[1].value.is_none() && parts[1].children.is_empty());
        }
        let (_, _, guardrows) = family_whole(&result, 1);
        let target = guardrows
            .iter()
            .find(|r| {
                matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::Evaluation {
                        applicability: "not_applicable",
                        ..
                    })
                )
            })
            .unwrap()
            .0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
        let mut changed = result.nodes[..=target].to_vec();
        let Some(Payload::Evaluation { parts, .. }) = &mut changed[target].payload else {
            unreachable!()
        };
        parts[1].value = Some(NodeRef(0));
        rejects_named_prefix(&result, &changed);

        let fact = Fact {
            snapshot: "v".into(),
            subject: "sample".into(),
            field: Some("Numeric.Sample.p".into()),
            atom: Some("p".into()),
        };
        let mut changed = result.nodes[..=domain].to_vec();
        assert!(changed[domain].support.is_empty());
        changed[domain].support.push(fact.clone());
        assert_ne!(changed[domain].support, result.nodes[domain].support);
        rejects_named_prefix(&result, &changed);
        let guarded_whole = result.answers[1].outputs["evaluation"].0;
        let mut changed = result.nodes[..=guarded_whole].to_vec();
        assert!(!changed[guarded_whole].support.is_empty());
        changed[guarded_whole].support.clear();
        assert_ne!(
            changed[guarded_whole].support,
            result.nodes[guarded_whole].support
        );
        rejects_named_prefix(&result, &changed);
        let earlier_proof = result.answers[0].evidence[0];
        for target in [target, result.answers[2].outputs["evaluation"].0] {
            assert!(earlier_proof.0 < target);
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
            let mut changed = result.nodes[..=target].to_vec();
            assert!(changed[target].evidence.is_empty());
            changed[target].evidence.push(earlier_proof);
            assert_ne!(changed[target].evidence, result.nodes[target].evidence);
            rejects_named_prefix(&result, &changed);
        }
        let mut scalar_order = result.nodes.clone();
        scalar_order[scalar.0].arguments[1..].reverse();
        rebuild_for_origin_and_support_recheck(&result, &scalar_order).unwrap();
        let (foreign_template, _, _) = family_whole(&result, 1);
        let (target_template, _, _) = family_whole(&result, 2);
        let Some(Payload::LawInstance {
            body: foreign_source,
            ..
        }) = &result.nodes[foreign_template].payload
        else {
            unreachable!()
        };
        let Some(Payload::LawInstance {
            body: target_source,
            ..
        }) = &result.nodes[target_template].payload
        else {
            unreachable!()
        };
        let Some(Payload::Expression {
            bindings: foreign_bindings,
            ..
        }) = &result.nodes[foreign_source.0].payload
        else {
            unreachable!()
        };
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target_source.0]).unwrap();
        let mut changed = result.nodes[..=target_source.0].to_vec();
        let Some(Payload::Expression { bindings, .. }) = &mut changed[target_source.0].payload
        else {
            unreachable!()
        };
        assert_ne!(bindings[0].value, foreign_bindings[0].value);
        bindings[0].value = foreign_bindings[0].value;
        changed[target_source.0].arguments[0] = foreign_bindings[0].value;
        rejects_named_prefix(&result, &changed);
        let (_, _, skiprows) = family_whole(&result, 2);
        let skip = skiprows[0].0;
        let skip_instance = result.nodes[skip].arguments[0].0;
        let Some(Payload::Evaluation {
            value: Some(skip_value),
            ..
        }) = &result.nodes[skip].payload
        else {
            unreachable!()
        };
        for index in [template, evaluation, skip_instance, skip_value.0, skip] {
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=index]).unwrap();
            let mut changed = result.nodes[..=index].to_vec();
            changed[index].rule = Rule::Construction("difference");
            rejects_named_prefix(&result, &changed);
            let mut changed = result.nodes[..=index].to_vec();
            changed[index]
                .reasons
                .push(Reason::internal("forged", "metadata".into()));
            rejects_named_prefix(&result, &changed);
        }
        let mut changed = result.nodes[..=skip].to_vec();
        let Some(Payload::Evaluation { parts, .. }) = &mut changed[skip].payload else {
            unreachable!()
        };
        parts[0].location = parts[1].location.clone();
        rejects_named_prefix(&result, &changed);

        // 適用wrapperを走査しても、生の元body producerだけを選ぶ。
        let mut graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let mut control = named_call_quiet();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        let (.., guardrows) = family_whole(&result, 1);
        let applicable = *guardrows
            .iter()
            .find(|r| {
                matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::Evaluation {
                        applicability: "applicable",
                        ..
                    })
                )
            })
            .unwrap();
        for (row, accept) in [(applicable, true), (NodeRef(skip), false)] {
            let instance = result.nodes[row.0].arguments[0];
            let Some(Payload::LawInstance { body, bindings, .. }) =
                &result.nodes[instance.0].payload
            else {
                unreachable!()
            };
            graph.active = result.contexts[row.0];
            let probe = Node {
                ty: NodeType::Expression(Type::Bool),
                payload: Some(Payload::Transform {
                    operation: TransformOp::Not,
                    operands: vec![*body],
                    bindings: bindings.clone(),
                }),
                rule: Rule::Construction("expression"),
                arguments: std::iter::once(*body)
                    .chain(bindings.iter().map(|b| b.value))
                    .collect(),
                support: vec![],
                evidence: vec![],
                judgment: None,
                scope: result.nodes[row.0].scope.clone(),
                reasons: vec![],
            };
            if accept {
                environment.validate(&graph, &probe).unwrap();
            } else {
                assert!(
                    matches!(
                        environment.validate(&graph, &probe),
                        Err(ValidationFailure::Internal(_))
                    ),
                    "NA body Sourceは実raw Evaluationの代わりにならない"
                );
            }
        }
    }
    #[test]
    fn finite_law_families_reject_equal_request_instance_and_call_producers() {
        let result = finite_family_example(
            "view keep(b:Bool): Bool = true; view twice(b:Bool): Bool = keep(b) and keep(b); view negative(b:Bool):Bool = false; law required success(b:Bool): twice(b); law required failure(b:Bool): negative(b);",
            &[
                "one=check(Calc.success)",
                "again=check(Calc.success)",
                "bad=check(Calc.failure)",
                "bad_again=check(Calc.failure)",
            ],
            false,
        );
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let projections: Vec<_> = result
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(i, n)| {
                (result.contexts[i].instance.is_some()
                    && result.contexts[i].frame.is_none()
                    && n.arguments.len() == 3
                    && matches!(n.payload, Some(Payload::Scalar(Scalar::Bool(false))))
                    && matches!(&n.rule, Rule::Input { kind: "law", .. }))
                .then_some(i)
            })
            .collect();
        let foreign = projections[0];
        let target = projections
            .iter()
            .copied()
            .find(|i| result.contexts[*i].request == 1)
            .unwrap();
        assert_ne!(
            result.contexts[target].request,
            result.contexts[foreign].request
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
        let mut changed = result.nodes[..=target].to_vec();
        changed[target].arguments = result.nodes[foreign].arguments.clone();
        rejects_named_prefix(&result, &changed);
        let calls: Vec<_> = result
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(i, n)| {
                let Some(Payload::Evaluation {
                    expression,
                    value: Some(_),
                    ..
                }) = &n.payload
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
                (result.contexts[i].request == 0
                    && result.contexts[i].frame.is_some()
                    && &result.prepared.inputs().sources().law().bytes()[span.0..span.1] == b"true")
                    .then_some(i)
            })
            .collect();
        assert_eq!(calls.len(), 4);
        let Some(Payload::Evaluation {
            value: Some(foreign_value),
            ..
        }) = &result.nodes[calls[0]].payload
        else {
            unreachable!()
        };
        for target in [calls[1], calls[2]] {
            assert_ne!(
                result.contexts[calls[0]].frame,
                result.contexts[target].frame
            );
            if target == calls[1] {
                assert_eq!(
                    result.contexts[calls[0]].instance,
                    result.contexts[target].instance
                );
            } else {
                assert_ne!(
                    result.contexts[calls[0]].instance,
                    result.contexts[target].instance
                );
            }
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
            let mut changed = result.nodes[..=target].to_vec();
            let Some(Payload::Evaluation { value, parts, .. }) = &mut changed[target].payload
            else {
                unreachable!()
            };
            assert_ne!(*value, Some(*foreign_value));
            *value = Some(*foreign_value);
            parts[0].value = Some(*foreign_value);
            *changed[target].arguments.last_mut().unwrap() = *foreign_value;
            rejects_named_prefix(&result, &changed);
        }
        let counters: Vec<_> = result
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(i, n)| {
                matches!(&n.payload, Some(Payload::Counterexample { .. })).then_some(i)
            })
            .collect();
        assert_eq!(counters.len(), 4);
        for target in [counters[1], counters[2]] {
            let foreign = counters[0];
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
            let mut changed = result.nodes[..=target].to_vec();
            changed[target].arguments = result.nodes[foreign].arguments.clone();
            changed[target].payload = result.nodes[foreign].payload.clone();
            changed[target].scope = result.nodes[foreign].scope.clone();
            rejects_named_prefix(&result, &changed);
        }
    }
    #[test]
    fn finite_law_families_keep_empty_domain_scope_and_unused_guard_bodies() {
        let sources = numeric_recheck_fixture(
            &["p"],
            "law required empty(e:Empty,b:Bool): e = e; law required skipped(b:Bool,s:Sample) when false: s.p; law required sets(s:Set<Bool>):s=s;",
        );
        let old = crate::definition::check_definitions(&[(
            "definition0",
            sources.definitions()[0].bytes(),
        )])
        .unwrap();
        let definitions=String::from_utf8(sources.definitions()[0].bytes().to_vec()).unwrap().replace("\"declarations\":[", "\"declarations\":[{\"kind\":\"entity\",\"name\":\"Numeric.Empty\",\"meaning\":\"空の対象族。\",\"parameters\":[],\"fields\":[],\"alignments\":[]},");
        let new = crate::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .unwrap();
        let old_digest = &old.vocabularies["Numeric"].digest;
        let new_digest = &new.vocabularies["Numeric"].digest;
        let law = String::from_utf8(sources.law().bytes().to_vec())
            .unwrap()
            .replace(old_digest, new_digest);
        let map = String::from_utf8(sources.archmap().bytes().to_vec())
            .unwrap()
            .replace(old_digest, new_digest);
        let result = evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![definitions.into_bytes()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &[
                "empty=check(Calc.empty)",
                "skipped=check(Calc.skipped,s=@v/sample)",
                "sets=check(Calc.sets)",
            ],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let (template, domain, rows) = family_whole(&result, 0);
        assert!(rows.is_empty());
        assert!(result.nodes[domain].scope.snapshots.contains("v"));
        assert_eq!(result.nodes[template].arguments.len(), 2);
        let proof = result.answers[0].evidence[0];
        assert!(
            matches!(&result.nodes[proof.0].payload,Some(Payload::FiniteExhaustion {checked:0,instances,..}) if instances.is_empty())
        );
        let mut changed = result.nodes[..=proof.0].to_vec();
        changed[domain].scope.snapshots.clear();
        rejects_named_prefix(&result, &changed);
        assert!(result.answers[1].reasons.is_empty());
        let (_, _, rows) = family_whole(&result, 1);
        assert_eq!(rows.len(), 2);
        for row in rows {
            let Some(Payload::Evaluation { parts, .. }) = &result.nodes[row.0].payload else {
                unreachable!()
            };
            assert!(parts[1].children.is_empty() && parts[1].value.is_none());
        }

        assert!(result.answers[1].evidence.iter().any(|r|matches!(&result.nodes[r.0].payload,Some(Payload::FiniteExhaustion {checked:2,instances,..}) if instances.len()==2)));
        let display = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(i, n)| {
                matches!(&n.payload,Some(Payload::Scalar(Scalar::Set {items,..})) if items.len()==2)
                    .then_some(i)
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

        let unknown = finite_family_example(
            "law required uncertain(s:Sample) when s.p:false; law required ensured(s:Sample) when s.p:true;",
            &[
                "uncertain=check(Calc.uncertain)",
                "ensured=check(Calc.ensured)",
            ],
            true,
        );
        assert_eq!(unknown.status(), "partial", "{:?}", unknown.issues);
        assert_eq!(unknown.answers[0].status, Decision::Undetermined);
        assert_eq!(unknown.answers[1].status, Decision::Established);
        rebuild_for_origin_and_support_recheck(&unknown, &unknown.nodes).unwrap();
        // 元観測の条件付き族を、補完後の回答rootと区別して元宣言・Contextから選ぶ。
        let original_rows = |request, name: &str| {
            let Signature::Law { body, .. } =
                &unknown.prepared.inputs().law().declarations[name].signature
            else {
                unreachable!()
            };
            let span = unknown.prepared.inputs().law().exprs[*body].span;
            let candidates: Vec<_> = unknown.nodes.iter().enumerate().filter_map(|(index,node)| {
                let context=unknown.contexts[index];
                if context.request!=request || context.case.is_some() || context.frame.is_some()
                    || context.instance.is_some() || context.iteration.is_some() {return None;}
                let Some(Payload::Evaluation {expression,parts,..})=&node.payload else {return None;};
                let instance=*node.arguments.first()?;
                let Some(Payload::LawInstance {name:actual,body:source,..})=&unknown.nodes[instance.0].payload else {return None;};
                if actual!=name || source!=expression {return None;}
                assert!(matches!(&unknown.nodes[source.0].payload,Some(Payload::Expression {location:Location::Law {span:actual},parameters,..}) if *actual==span && parameters.len()==1 && parameters[0].0=="s"));
                Some(parts[0].children.clone())
            }).collect();
            assert_eq!(candidates.len(), 1, "unique original whole family: {name}");
            candidates.into_iter().next().unwrap()
        };
        // 回答rootはBool補完2caseのwhole族を指す。各caseの元Ref族は一行のままである。
        for (request, name) in [(0, "Calc.uncertain"), (1, "Calc.ensured")] {
            let evaluation = &unknown.nodes[unknown.answers[request].outputs["evaluation"].0];
            assert!(matches!(
                &unknown.nodes[evaluation.arguments[0].0].payload,
                Some(Payload::CompletionSeed { .. })
            ));
            let Some(Payload::Evaluation { parts, .. }) = &evaluation.payload else {
                unreachable!()
            };
            let cases = &parts[0].children;
            assert_eq!(cases.len(), 2);
            let mut values = Vec::new();
            for case in cases {
                let context = unknown.contexts[case.0];
                assert_eq!(context.request, request);
                assert!(
                    context.case.is_some()
                        && context.frame.is_none()
                        && context.instance.is_none()
                        && context.iteration.is_none()
                );
                let whole = &unknown.nodes[case.0];
                assert!(
                    matches!(&unknown.nodes[whole.arguments[0].0].payload,Some(Payload::LawInstance {name:actual,..}) if actual==name)
                );
                let Some(Payload::Evaluation {
                    parts,
                    value: Some(value),
                    ..
                }) = &whole.payload
                else {
                    panic!("known whole family in completion")
                };
                assert_eq!(parts[0].children.len(), 1);
                let Scalar::Bool(value) = data_scalar_at(&unknown, value.0) else {
                    unreachable!()
                };
                values.push(*value);
                let propositions: Vec<_> = unknown
                    .nodes
                    .iter()
                    .enumerate()
                    .filter_map(|(i, node)| {
                        (unknown.contexts[i] == context
                            && matches!(&node.payload, Some(Payload::Proposition { .. }))
                            && node.arguments.get(1) == Some(case))
                        .then_some(node)
                    })
                    .collect();
                assert_eq!(propositions.len(), 1);
                assert_eq!(
                    propositions[0].judgment.as_ref().unwrap().status,
                    if *value {
                        Decision::Established
                    } else {
                        Decision::Refuted
                    }
                );
            }
            if request == 0 {
                assert!(values.contains(&true) && values.contains(&false));
                assert!(unknown.answers[request].evidence.iter().any(|r| matches!(
                    &unknown.nodes[r.0].payload,
                    Some(Payload::CompletionPair { .. })
                )));
            } else {
                assert_eq!(values, vec![true, true]);
                assert!(unknown.answers[request].evidence.iter().any(|r|matches!(&unknown.nodes[r.0].payload,Some(Payload::FiniteExhaustion {checked:2,instances,..}) if instances.len()==cases.len() && instances.iter().all(|instance|cases.contains(instance)))));
            }
        }
        let rows = original_rows(0, "Calc.uncertain");
        assert_eq!(rows.len(), 1);
        let row = rows[0].0;
        let Some(Payload::Evaluation {
            expression,
            parts,
            value,
            applicability,
            ..
        }) = &unknown.nodes[row].payload
        else {
            unreachable!()
        };
        assert_eq!(*applicability, "undetermined");
        assert!(value.is_none());
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0].children.len(), 1);
        assert_eq!(parts[1].children.len(), 1);
        assert!(matches!(
            unknown.nodes[expression.0].payload,
            Some(Payload::Transform { .. })
        ));
        rebuild_for_origin_and_support_recheck(&unknown, &unknown.nodes[..=row]).unwrap();
        let Some(Payload::LawInstance { body: raw_body, .. }) =
            &unknown.nodes[unknown.nodes[row].arguments[0].0].payload
        else {
            unreachable!()
        };
        let mut changed = unknown.nodes[..=row].to_vec();
        let Some(Payload::Transform { operands, .. }) = &mut changed[expression.0].payload else {
            unreachable!()
        };
        operands[0] = *raw_body;
        changed[expression.0].arguments[0] = *raw_body;
        rejects_named_prefix(&unknown, &changed);
        let ensured = original_rows(1, "Calc.ensured");
        let ensured = ensured[0].0;
        let Some(Payload::Evaluation {
            expression: target,
            value: Some(scalar),
            ..
        }) = &unknown.nodes[ensured].payload
        else {
            unreachable!()
        };
        rebuild_for_origin_and_support_recheck(&unknown, &unknown.nodes[..=scalar.0]).unwrap();
        let Some(Payload::Evaluation {
            bindings: foreign, ..
        }) = &unknown.nodes[row].payload
        else {
            unreachable!()
        };
        rebuild_for_origin_and_support_recheck(&unknown, &unknown.nodes[..=target.0]).unwrap();
        let mut changed = unknown.nodes[..=target.0].to_vec();
        let Some(Payload::Transform { bindings, .. }) = &mut changed[target.0].payload else {
            unreachable!()
        };
        assert_ne!(bindings[0].value, foreign[0].value);
        bindings[0].value = foreign[0].value;
        *changed[target.0].arguments.last_mut().unwrap() = foreign[0].value;
        rejects_named_prefix(&unknown, &changed);
    }

    #[test]
    fn finite_law_family_actual_domain_product_row_evidence_and_recheck_stops() {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{
            cell::{Cell, RefCell},
            rc::Rc,
        };
        let sources = numeric_recheck_fixture(
            &["p"],
            "view seed():Z = 7; view hole(s:Sample):Bool = s.p; law required prior(b:Bool):false; law required current(a:Bool,b:Bool):true;",
        );
        let asks = [
            "seed=evaluate(Calc.seed)",
            "prior=check(Calc.prior)",
            "hole=evaluate(Calc.hole,s=@v/sample)",
            "current=check(Calc.current)",
            "later=evaluate(Calc.seed)",
        ];
        let mut normal_control = named_call_quiet();
        let prepared = prepare_observed(sources.clone(), &asks, &mut normal_control).unwrap();
        let target = prepared.inputs().law().declarations["Calc.current"].span;
        let context = super::super::call::Context {
            request: 3,
            frame: None,
            iteration: None,
            instance: None,
            case: None,
        };
        let progress = Rc::new(RefCell::new(Vec::new()));
        let observed = progress.clone();
        let normal = evaluate_observed_with_validator(
            prepared,
            &mut normal_control,
            |environment, graph, request, answer| {
                environment.validate_answer(graph, request, answer)?;
                if request.id == "hole" {
                    let observed = observed.clone();
                    data::observe_iterations(move |span, actual, phase, index| {
                        if span == target && actual == context && phase.starts_with("family_") {
                            observed.borrow_mut().push((phase, index));
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
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        let normal_wire = normal.wire();
        let Json::Obj(ref normal_fields) = normal_wire else {
            unreachable!()
        };
        let Json::Arr(normal_answers) = &normal_fields["answers"] else {
            unreachable!()
        };
        // 五つの実phaseの一点ずつ。全phase×停止種別×位置の走査はしない。
        for (phase, position, kind) in [
            ("family_enum", 1, 0),
            ("family_product", 1, 2),
            ("family_row", 1, 1),
            ("family_exhaustion", 0, 2),
            ("family_recheck", 1, 0),
        ] {
            let baseline: Vec<_> = progress
                .borrow()
                .iter()
                .filter_map(|(actual, index)| (*actual == phase).then_some(*index))
                .collect();
            assert!(baseline.contains(&position), "{phase}: {baseline:?}");
            if position == 1 {
                assert!(baseline.starts_with(&[0, 1]), "{phase}: {baseline:?}");
            }
            let (limits, usage, expected) = match kind {
                0 => (
                    Limits {
                        time_ms: Some(1),
                        memory_mib: None,
                    },
                    Usage {
                        elapsed_ms: 2,
                        ..Usage::default()
                    },
                    StopReason::BudgetExhausted {
                        resource: Resource::TimeMs,
                        limit: 1,
                        observed: 2,
                    },
                ),
                1 => (
                    Limits {
                        time_ms: None,
                        memory_mib: Some(1),
                    },
                    Usage {
                        memory_mib: 2,
                        ..Usage::default()
                    },
                    StopReason::BudgetExhausted {
                        resource: Resource::MemoryMib,
                        limit: 1,
                        observed: 2,
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
            let prepared = prepare_observed(sources.clone(), &asks, &mut control).unwrap();
            let seen = Rc::new(RefCell::new(Vec::new()));
            let observed = seen.clone();
            let stopped = evaluate_observed_with_validator(
                prepared,
                &mut control,
                |environment, graph, request, answer| {
                    environment.validate_answer(graph, request, answer)?;
                    if request.id == "hole" {
                        let (armed, observed) = (armed.clone(), observed.clone());
                        data::observe_iterations(move |span, actual, operation, index| {
                            if span == target && actual == context && operation == phase {
                                observed.borrow_mut().push(index);
                                if index == position {
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
            assert_eq!(seen.borrow().last(), Some(&position), "{phase}");
            assert_eq!(
                stopped.status(),
                "interrupted",
                "{phase}: {:?}",
                stopped.issues
            );
            assert_eq!(control.stop_reason(), Some(expected.clone()));
            assert_eq!(Some(probes.get()), frozen.get());
            let wire = stopped.wire();
            let Json::Obj(ref fields) = wire else {
                unreachable!()
            };
            let Json::Arr(answers) = &fields["answers"] else {
                unreachable!()
            };
            assert_eq!(&answers[..3], &normal_answers[..3], "{phase}");
            assert_eq!(stopped.answers[3].status, Decision::Undetermined);
            assert!(stopped.answers[3].claim.is_none() && stopped.answers[3].evidence.is_empty());
            if phase == "family_exhaustion" {
                assert!(stopped.answers[3].outputs.contains_key("evaluation"));
            } else {
                assert!(stopped.answers[3].outputs.is_empty());
            }
            assert!(stopped.answers[4].outputs.is_empty());
            for answer in &stopped.answers[3..] {
                let reason = answer
                    .reasons
                    .iter()
                    .find(|r| matches!(&r.kind,ReasonKind::Stop(actual) if actual==&expected))
                    .unwrap();
                let expected_wire = expected.wire();
                let Json::Obj(ref expected_fields) = expected_wire else {
                    unreachable!()
                };
                let reason_wire = reason.wire();
                let Json::Obj(ref reason_fields) = reason_wire else {
                    unreachable!()
                };
                assert_eq!(reason_fields.get("details"), expected_fields.get("details"));
                assert!(
                    !answer
                        .reasons
                        .iter()
                        .any(|r| matches!(r.kind, ReasonKind::Internal(_)))
                );
            }
            assert!(
                stopped
                    .nodes
                    .iter()
                    .enumerate()
                    .any(|(i, n)| stopped.contexts[i].request == 1
                        && matches!(n.payload, Some(Payload::Counterexample { .. })))
            );
            assert!(
                !stopped
                    .nodes
                    .iter()
                    .enumerate()
                    .any(|(i, n)| stopped.contexts[i].request == 3
                        && matches!(n.payload, Some(Payload::FiniteExhaustion { .. })))
            );
            assert!(!stopped.contexts.iter().any(|c| c.request == 4));
            if phase == "family_row" {
                assert!(
                    stopped
                        .nodes
                        .iter()
                        .enumerate()
                        .any(|(i, n)| stopped.contexts[i].request == 3
                            && n.ty == NodeType::LawInstance)
                );
            }
            rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
            let before = probes.get();
            assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
            assert_eq!(probes.get(), before);
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

    fn original_view_evaluation_for_answer(result: &ObservedEvaluation, id: &str) -> NodeRef {
        let request = result
            .answers
            .iter()
            .position(|answer| answer.id == id)
            .unwrap();
        let declaration = result.prepared.requests().requests()[request].declaration();
        let Signature::View { body, .. } =
            &result.prepared.inputs().law().declarations[declaration].signature
        else {
            unreachable!()
        };
        let span = result.prepared.inputs().law().exprs[*body].span;
        let candidates:Vec<_>=result.nodes.iter().enumerate().filter_map(|(index,node)| {
            let context=result.contexts[index];
            (context.request==request && context.case.is_none() && context.frame.is_none() && context.iteration.is_none() && context.instance.is_none()
                && matches!(&node.payload,Some(Payload::Evaluation {expression,..}) if matches!(&result.nodes[expression.0].payload,Some(Payload::Expression {location:Location::Law {span:actual},..}) if *actual==span)))
                .then_some(NodeRef(index))
        }).collect();
        assert_eq!(candidates.len(), 1, "unique original view root: {id}");
        candidates[0]
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
            let root = original_view_evaluation_for_answer(&result, &answer.id);
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
    fn named_calls_complete_bool_ref_choices_and_keep_other_missing_at_callee_source() {
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
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        let partial = evaluate_observed_bytes(
            sources,
            &["v=evaluate(Calc.caller,s=@v/sample,t=@v/other)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(partial.status(), "partial", "{:?}", partial.issues);
        assert_eq!(partial.answers[0].status, Decision::Undetermined);
        assert!(!partial.answers[0].outputs.contains_key("value"));
        assert!(partial.answers[0].claim.is_none());
        for (subject, field) in [
            ("sample", "Numeric.Sample.p"),
            ("other", "Numeric.Sample.q"),
        ] {
            assert!(
                partial.answers[0]
                    .reasons
                    .iter()
                    .flat_map(|r| &r.missing)
                    .any(|f| f.subject == subject && f.field.as_deref() == Some(field))
            );
        }
        let values: Vec<_> = partial
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(i, node)| {
                (partial.contexts[i].case.is_some()
                    && partial.contexts[i].frame.is_some()
                    && matches!(&node.rule, Rule::Input { kind: "atom", .. })
                    && matches!(&node.payload, Some(Payload::Scalar(Scalar::Q(_, _)))))
                .then_some(i)
            })
            .collect();
        assert_eq!(values.len(), 1);
        assert!(
            matches!(&partial.nodes[values[0]].payload,Some(Payload::Scalar(Scalar::Q(n,d))) if n==&(-2).into() && d==&3.into())
        );
        assert!(partial.nodes.iter().any(|node|matches!(&node.payload,Some(Payload::Expression {location:Location::Law {span},bindings,..}) if &law[span.0..span.1]==b"x.q" && bindings.iter().any(|b|b.name=="x"))));
        rebuild_for_origin_and_support_recheck(&partial, &partial.nodes).unwrap();
        rebuild_for_origin_and_support_recheck(&partial, &partial.nodes[..=values[0]]).unwrap();
        let mut changed = partial.nodes[..=values[0]].to_vec();
        changed[values[0]].scope.readings.insert("Foreign".into());
        rejects_named_prefix(&partial, &changed);
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
        let finite = evaluate_observed_bytes(
            numeric_recheck_fixture(&[], "view quantify(): Bool = forall item: Bool. item; view caller(): Bool = quantify();"),
            &["v=evaluate(Calc.caller)"], &mut named_call_quiet(),
        ).unwrap();
        assert_eq!(finite.status(), "complete", "{:?}", finite.issues);
        assert_eq!(
            data_scalar_at(&finite, finite.answers[0].outputs["value"].0),
            &Scalar::Bool(false)
        );
        rebuild_for_origin_and_support_recheck(&finite, &finite.nodes).unwrap();
        let sources = numeric_recheck_fixture(
            &[],
            r#"
 view unsupported(s: Sample): Bool = forall item: Z. item=0;
 view caller(s: Sample): Bool = unsupported(s);
"#,
        );
        let law = sources.law().bytes().to_vec();
        let quantified = evaluate_observed_bytes(
            sources,
            &["v=evaluate(Calc.caller,s=@v/sample)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(quantified.status(), "complete", "{:?}", quantified.issues);
        assert_eq!(
            data_scalar_at(&quantified, quantified.answers[0].outputs["value"].0),
            &Scalar::Bool(false)
        );
        rebuild_for_origin_and_support_recheck(&quantified, &quantified.nodes).unwrap();
        let checked = quantified.prepared.inputs().law();
        let callee = &checked.declarations["Calc.unsupported"];
        let Signature::View { body, .. } = &callee.signature else {
            unreachable!()
        };
        let span = checked.exprs[*body].span;
        let ExprKind::Quant {
            kind: crate::law::ast::QuantKind::Forall,
            var,
            split:
                crate::law::ast::QuantSplit::Fixed {
                    domain: crate::law::ast::QuantDomain::Type(_),
                    body: equation,
                },
        } = &checked.exprs[*body].kind
        else {
            unreachable!()
        };
        assert_eq!(var.name, "item");
        assert_eq!(checked.quantifier_types[*body], Some(Type::Z));
        let normalization = quantified.nodes.iter().enumerate().find_map(|(index,node)| {
            let Some(Payload::Normalization {before,..})=&node.payload else {return None};
            (quantified.contexts[index].frame.is_some()
                && matches!(&quantified.nodes[before.0].payload,
                    Some(Payload::Expression {location:Location::Law {span:actual},..}) if *actual==span))
                .then_some(index)
        }).unwrap();
        let Some(Payload::Normalization {
            before,
            after,
            steps,
        }) = &quantified.nodes[normalization].payload
        else {
            unreachable!()
        };
        let Some(Payload::Expression {
            location: Location::Law { span },
            parameters,
            ..
        }) = &quantified.nodes[before.0].payload
        else {
            unreachable!()
        };
        assert_eq!(&law[span.0..span.1], b"forall item: Z. item=0");
        assert!(parameters.is_empty(), "元forallはitemを束縛する");
        assert_eq!(data_scalar_at(&quantified, after.0), &Scalar::Bool(false));
        assert_eq!(steps.len(), 2);
        assert!(matches!(
            &quantified.nodes[steps[0].0].payload,
            Some(Payload::ParameterizedTransform {
                operation: TransformOp::Difference,
                ..
            })
        ));
        assert_eq!(
            quantified.nodes[steps[0].0].ty,
            NodeType::Expression(Type::Z)
        );
        let context = quantified.contexts[before.0];
        let frame = &quantified.frames[context.frame.unwrap()];
        assert_eq!(frame.arguments.len(), 1);
        let Some(Payload::Expression {
            location: Location::Law { span: call_span },
            ..
        }) = &quantified.nodes[frame.source.0].payload
        else {
            unreachable!()
        };
        assert_eq!(&law[call_span.0..call_span.1], b"unsupported(s)");
        let domain = quantified
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (quantified.contexts[index] == context
                    && matches!(&node.payload, Some(Payload::TypeDomain { ty: Type::Z }))
                    && node.arguments == [*before])
                .then_some(index)
            })
            .unwrap();
        assert!(matches!(&quantified.nodes[domain].rule,
            Rule::Input {kind:"law",location:Location::Law {span}} if *span==var.span));
        let ExprKind::Binary { lhs, rhs, .. } = &checked.exprs[*equation].kind else {
            unreachable!()
        };
        for original in [*body, *equation, *lhs, *rhs] {
            assert!(quantified.nodes.iter().enumerate().any(|(index,node)| {
                quantified.contexts[index]==context
                    && matches!(&node.payload,Some(Payload::Expression {location:Location::Law {span},..})
                        if *span==checked.exprs[original].span)
            }), "calleeの元AST出現を保持する");
        }
        let whole = quantified
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (matches!(&node.payload,Some(Payload::Evaluation {expression,value:Some(value),..})
                if expression==before && value==after)
                    && node.evidence == [NodeRef(normalization)])
                .then_some(index)
            })
            .unwrap();
        assert!(
            quantified.nodes[whole]
                .scope
                .quantifiers
                .iter()
                .any(|quantifier| {
                    quantifier.name == var.name
                        && quantifier.ty == Type::Z
                        && quantifier.occurrence == var.span
                        && quantifier.domain == Some(NodeRef(domain))
                        && quantifier.context == Some(context)
                })
        );
        for target in [domain, steps[0].0, normalization, whole] {
            rebuild_for_origin_and_support_recheck(&quantified, &quantified.nodes[..=target])
                .unwrap();
        }
        let sources = numeric_recheck_fixture(
            &[],
            r#"
 view unsupported(s: Sample): Bool = exists item: Z. item=0;
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
        assert_eq!(&law[span.0..span.1], b"exists item: Z. item=0");
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
            instance: None,
            case: None,
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
                instance: None,
                case: None,
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
            domain,
            filter: Some(filter),
            ..
        } = prepared.inputs().law().exprs[*body].kind
        else {
            unreachable!()
        };
        let domain_span = prepared.inputs().law().exprs[domain].span;
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
            instance: None,
            case: None,
        };
        let first_filter_iteration = Rc::new(Cell::new(None));
        let first_filter = first_filter_iteration.clone();
        let event = move |span, context: super::super::call::Context, name: &str, index| {
            if span == target && context == parent && name == "comprehension_iteration" {
                Some(("iteration", index))
            } else if span == filter_literal
                && context.request == parent.request
                && context.case == parent.case
                && context.frame == parent.frame
                && context.instance == parent.instance
                && context.iteration.is_some()
                && name == "expression"
            {
                let iteration = context.iteration.unwrap();
                let first = first_filter.get().unwrap_or_else(|| {
                    first_filter.set(Some(iteration));
                    iteration
                });
                (iteration == first).then_some(("filter", 0))
            } else if span == target && context == parent && name == "set" {
                Some(("set", index))
            } else {
                None
            }
        };
        let seen = Rc::new(RefCell::new(Vec::new()));
        let progress = seen.clone();
        let baseline_event = event.clone();
        data::observe_iterations(move |span, context, name, index| {
            if let Some(event) = baseline_event(span, context, name, index) {
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
        let first:Vec<_>=normal.iterations.iter().enumerate().filter(|(_,iteration)| {
            iteration.caller==parent && matches!(&iteration.member,super::super::call::Member::ListPosition(0))
                && matches!(&normal.nodes[iteration.source.0].payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==target)
                && matches!(&normal.nodes[iteration.domain.0].payload,Some(Payload::Evaluation {expression,..}) if matches!(&normal.nodes[expression.0].payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==domain_span))
        }).collect();
        assert_eq!(first.len(), 1);
        let (first_iteration, iteration) = first[0];
        assert_eq!(first_filter_iteration.get(), Some(first_iteration));
        let first_domain = iteration.domain.0;
        let original_scalar = |span, context| {
            let scalars:Vec<_>=normal.nodes.iter().enumerate().filter_map(|(index,node)| {
                (normal.contexts[index]==context && matches!(&node.payload,Some(Payload::Scalar(_)))
                    && matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span:actual}} if *actual==span)).then_some(index)
            }).collect();
            assert_eq!(scalars.len(), 1, "unique original Scalar at {span:?}");
            scalars[0]
        };
        let filter_scalar = original_scalar(
            filter_literal,
            super::super::call::Context {
                iteration: Some(first_iteration),
                ..parent
            },
        );
        let result_scalar = original_scalar(target, parent);
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
                        let event = event.clone();
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
        // Keep the original regression test identity; known Map container values are now supported.
        let result = evaluate_observed_bytes(
            sources.clone(),
            &["value=evaluate(Calc.deferred)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete");
        let answer = &result.answers[0];
        assert_eq!(answer.status, Decision::Established);
        let Some(Payload::Scalar(Scalar::Set { element, items })) =
            &result.nodes[answer.outputs["value"].0].payload
        else {
            panic!("typed empty Set")
        };
        assert!(items.is_empty());
        let sample = Type::Ref("Numeric.Sample".into());
        assert_eq!(
            *element,
            Type::List(Box::new(Type::Map(
                Box::new(sample.clone()),
                Box::new(sample)
            )))
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
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
        let mut pattern = BTreeMap::new();
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
                assert_eq!(context.case, origin.case);
                assert!(context.iteration.is_some());
                if bytes.get(span.0..span.1) == Some(b"y") {
                    nested += 1;
                    assert!(context.case.is_none());
                    assert!(origin.iteration.is_some(), "外側反復のRHSをrootへ戻さない");
                    assert_eq!(result.iterations[context.iteration.unwrap()].caller, origin);
                    let Some(Payload::Evaluation { value: rhs, .. }) =
                        &result.nodes[input.0].payload
                    else {
                        unreachable!()
                    };
                    assert_eq!(value, rhs, "元RHS Scalarをそのまま参照する");
                } else {
                    *pattern.entry(context.case).or_insert(0usize) += 1;
                    assert_eq!(origin.iteration, None);
                    let scalar = value.unwrap();
                    assert_eq!(result.nodes[scalar.0].arguments, vec![input]);
                    assert_eq!(
                        result.nodes[input.0].scope.completions,
                        origin.case.is_some()
                    );
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
        assert_eq!(nested, 4);
        assert_eq!(pattern.get(&None), Some(&2));
        let evaluation = &result.nodes[result.answers[1].outputs["evaluation"].0];
        assert!(matches!(
            &result.nodes[evaluation.arguments[0].0].payload,
            Some(Payload::CompletionSeed { .. })
        ));
        let Some(Payload::Evaluation { parts, .. }) = &evaluation.payload else {
            unreachable!()
        };
        let cases = &parts[0].children;
        assert_eq!(cases.len(), 2);
        assert_eq!(pattern.len(), 1 + cases.len());
        for case in cases {
            let context = result.contexts[case.0];
            assert_eq!(context.request, 1);
            assert!(
                context.case.is_some()
                    && context.frame.is_none()
                    && context.instance.is_none()
                    && context.iteration.is_none()
            );
            assert_eq!(pattern.get(&context.case), Some(&2));
            let Some(Payload::Evaluation {
                value: Some(value), ..
            }) = &result.nodes[case.0].payload
            else {
                panic!("known pattern result in Bool case")
            };
            assert_eq!(data_scalar_at(&result, value.0), &set(&[11, 12]));
        }
        assert!(result.answers[1].evidence.iter().any(|r|matches!(&result.nodes[r.0].payload,Some(Payload::FiniteExhaustion {checked:2,instances,..}) if instances.len()==cases.len() && instances.iter().all(|instance|cases.contains(instance)))));
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
    fn plain_ref_fixture(changed_provenance: bool) -> InputSources {
        let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Roster","version":"1","dependencies":[],"declarations":[
{"kind":"entity","name":"Roster.Root","meaning":"所属先。","parameters":[],"fields":[],"alignments":[]},
{"kind":"entity","name":"Roster.E","meaning":"登録対象。","parameters":[{"name":"owner","type":["Ref","Roster.Root"],"meaning":"所属先。"}],"fields":[{"name":"flag","type":"Bool","meaning":"条件。"}],"alignments":[]},
{"kind":"entity","name":"Roster.Other","meaning":"異なる型。","parameters":[],"fields":[],"alignments":[]},
{"kind":"entity","name":"Roster.Empty","meaning":"空の登録族。","parameters":[],"fields":[],"alignments":[]},
{"kind":"data","name":"Roster.At","meaning":"登録対象を含む値。","constructors":[{"name":"NoneCase","arguments":[],"meaning":"参照なし。"},{"name":"At","arguments":[["Ref","Roster.E"]],"meaning":"参照あり。"}]}]}]}"#;
        let checked =
            crate::definition::check_definitions(&[("definition0", definitions.as_bytes())])
                .unwrap();
        let digest = &checked.vocabularies["Roster"].digest;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Calc {{
 use vocabulary Roster version "1" digest "{digest}";
 view all(): Bool = forall r:E . r=r;
 view powers(): Bool = forall item:Set<E> . item=item;
 view voidproduct(): Bool = forall item:(Empty,E) . true;
 view negative(): Bool = forall r:E . r.flag;
 law required called(): negative();
 law required both(): negative() and negative();
 view observe(s:E): Bool = s.flag;
 view full(): Bool = forall r:E . true;
 view construct(): Bool = forall item:(E,Bool) . true;
 view later(): Z = 9;
}}
"#
        );
        let modes = if changed_provenance {
            ["specification", "specification", "specification"]
        } else {
            ["specification", "proposed", "observed"]
        };
        let revision = if changed_provenance { "r2" } else { "r1" };
        let map = format!(
            r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Roster","version":"1","digest":"{digest}"}}],
"sources":[{{"id":"scan","uri":"urn:fixture:plain-ref-roster","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
"origins":[{{"id":"ov","mode":"{}","method":"最初の登録表。","locations":[{{"source":"scan","path":"v.model","span":[0,1]}}]}},{{"id":"ow","mode":"{}","method":"次の登録表。","locations":[{{"source":"scan","path":"w.model","span":[2,3]}}]}},{{"id":"oz","mode":"{}","method":"空の登録表。","locations":[{{"source":"scan","path":"z.model","span":[4,5]}}]}}],
"snapshots":[{{"id":"v","origin":"ov","subjects":[{{"id":"root","type":"Roster.Root","origin":"ov"}},{{"id":"item","type":"Roster.E","origin":"ov"}},{{"id":"other","type":"Roster.Other","origin":"ov"}}],"atoms":[]}},
{{"id":"w","origin":"ow","subjects":[{{"id":"root","type":"Roster.Root","origin":"ow"}},{{"id":"item","type":"Roster.E","origin":"ow"}}],"atoms":[{{"id":"flag","subject":"item","field":"Roster.E.flag","value":false,"origin":"ow"}}]}},
{{"id":"z","origin":"oz","subjects":[],"atoms":[]}}]}}"#,
            modes[0], modes[1], modes[2]
        );
        InputSources::from_bytes(
            vec![definitions.as_bytes().to_vec()],
            law.into_bytes(),
            map.into_bytes(),
        )
    }
    fn plain_ref_example(asks: &[&str]) -> ObservedEvaluation {
        evaluate_observed_bytes(plain_ref_fixture(false), asks, &mut named_call_quiet()).unwrap()
    }
    #[test]
    fn plain_ref_domains_recheck_snapshot_identity_scope_support_and_empty_products() {
        let asks = [
            "first=evaluate(Calc.all)",
            "again=evaluate(Calc.all)",
            "empty=evaluate(Calc.voidproduct)",
        ];
        let result = plain_ref_example(&asks);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let reject = |nodes: &[Node], stage: String| {
            let failure = rebuild_for_origin_and_support_recheck(&result, nodes).err();
            assert!(
                matches!(&failure, Some(ValidationFailure::Internal(_))),
                "{stage}: {failure:?}"
            );
        };
        let domain = in_domain(&result, 0);
        let Some(Payload::Domain { ty, elements }) = &result.nodes[domain].payload else {
            unreachable!()
        };
        assert_eq!(ty, &Type::Ref("Roster.E".into()));
        assert_eq!(elements.len(), 2);
        assert_eq!(
            data_scalar_at(&result, elements[0].0),
            &Scalar::Subject {
                snapshot: "v".into(),
                subject: "item".into(),
                entity: "Roster.E".into()
            }
        );
        assert_eq!(
            data_scalar_at(&result, elements[1].0),
            &Scalar::Subject {
                snapshot: "w".into(),
                subject: "item".into(),
                entity: "Roster.E".into()
            }
        );
        let facts = vec![
            Fact {
                snapshot: "v".into(),
                subject: "item".into(),
                field: None,
                atom: None,
            },
            Fact {
                snapshot: "w".into(),
                subject: "item".into(),
                field: None,
                atom: None,
            },
        ];
        assert_eq!(result.nodes[domain].support, facts);
        assert_eq!(
            result.nodes[domain].scope.snapshots,
            ["v".into(), "w".into(), "z".into()].into_iter().collect()
        );
        assert_eq!(
            result.nodes[domain].scope.modes,
            ["specification".into(), "proposed".into(), "observed".into()]
                .into_iter()
                .collect()
        );
        let empty = in_domain(&result, 2);
        assert!(
            matches!(&result.nodes[empty].payload,Some(Payload::Domain {elements,..}) if elements.is_empty())
        );
        assert_eq!(result.nodes[empty].support, facts);
        assert_eq!(
            result.nodes[empty].scope.snapshots,
            result.nodes[domain].scope.snapshots
        );
        assert_eq!(
            result.nodes[result.answers[2].outputs["value"].0].support,
            facts
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=domain]).unwrap();
        for mutation in 0..6 {
            let mut changed = result.nodes[..=domain].to_vec();
            match mutation {
                0 => {
                    changed[elements[1].0].payload = Some(Payload::Scalar(
                        data_scalar_at(&result, elements[0].0).clone(),
                    ));
                }
                1 => {
                    let Some(Payload::Domain { elements, .. }) = &mut changed[domain].payload
                    else {
                        unreachable!()
                    };
                    elements.pop();
                    let refs = elements.clone();
                    changed[domain].arguments.truncate(1);
                    changed[domain].arguments.extend(refs);
                }
                2 => {
                    let Some(Payload::Domain { elements, .. }) = &mut changed[domain].payload
                    else {
                        unreachable!()
                    };
                    elements[1] = elements[0];
                    let refs = elements.clone();
                    changed[domain].arguments.truncate(1);
                    changed[domain].arguments.extend(refs);
                }
                3 => {
                    changed[domain].scope.snapshots.remove("z");
                }
                4 => {
                    changed[domain].support.pop();
                }
                _ => {
                    let Some(Payload::Domain { ty, .. }) = &mut changed[domain].payload else {
                        unreachable!()
                    };
                    *ty = Type::Ref("Roster.Other".into());
                }
            }
            reject(&changed, format!("Domain variant {mutation}"));
        }
        let member = elements[0].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=member]).unwrap();
        for mutation in 0..2 {
            let mut changed = result.nodes[..=member].to_vec();
            let scalar = if mutation == 0 {
                Scalar::Subject {
                    snapshot: "z".into(),
                    subject: "item".into(),
                    entity: "Roster.E".into(),
                }
            } else {
                Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "other".into(),
                    entity: "Roster.Other".into(),
                }
            };
            changed[member].ty = NodeType::Value(scalar.ty());
            changed[member].payload = Some(Payload::Scalar(scalar));
            reject(&changed, format!("member Scalar variant {mutation}"));
        }
        let binder = iteration_binder_scalar_for_name(&result, 1, b"r");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=binder]).unwrap();
        let mut changed = result.nodes[..=binder].to_vec();
        changed[binder].payload = Some(Payload::Scalar(
            data_scalar_at(&result, elements[0].0).clone(),
        ));
        reject(&changed, "binder same-ID foreign snapshot".into());
        let source = result.nodes[domain].arguments[0].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source]).unwrap();
        let mut changed = result.nodes[..=source].to_vec();
        // raw AST Sourceは空支持。rosterの支持は元Source再分析から域へ導く。
        assert!(result.nodes[source].support.is_empty());
        changed[source].support.push(facts[0].clone());
        assert_ne!(changed[source].support, result.nodes[source].support);
        reject(&changed, "raw Source injected subject Fact".into());
        let changed =
            evaluate_observed_bytes(plain_ref_fixture(true), &asks, &mut named_call_quiet())
                .unwrap();
        assert_eq!(changed.status(), result.status());
        rebuild_for_origin_and_support_recheck(&changed, &changed.nodes).unwrap();
        for (original, new) in result.answers.iter().zip(&changed.answers) {
            assert_eq!(original.status, new.status);
            assert_eq!(
                data_scalar_at(&result, original.outputs["value"].0),
                data_scalar_at(&changed, new.outputs["value"].0)
            );
        }
        let changed_domain = in_domain(&changed, 0);
        assert_eq!(changed.nodes[changed_domain].support, facts);
        assert_eq!(
            changed.nodes[changed_domain].scope.modes,
            ["specification".into()].into_iter().collect()
        );
        assert_eq!(
            changed.prepared.inputs().archmap().sources[0].revision,
            "r2"
        );
        plain_ref_owned_type_syntax_stays_distinct_from_plain_roster();
    }
    fn plain_ref_owned_type_syntax_stays_distinct_from_plain_roster() {
        let sources = plain_ref_fixture(false);
        let law = String::from_utf8(sources.law().bytes().to_vec())
            .unwrap()
            .replace(
                " view later(): Z = 9;",
                r#" view later(): Z = 9;
 view plain(root:Root): Bool = forall r:E . true;
 view owned(root:Root): Bool = forall r:E[root] . true;
 view nested_owned(root:Root): Bool = exists packed:(Unit,Option<Set<E[root]>>) . false;
"#,
            );
        let sources = InputSources::from_bytes(
            sources
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            law.as_bytes().to_vec(),
            sources.archmap().bytes().to_vec(),
        );
        let normal = evaluate_observed_bytes(
            sources.clone(),
            &["normal=evaluate(Calc.plain,root=@v/root)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(normal.status(), "complete", "{:?}", normal.issues);
        assert_eq!(
            data_scalar_at(&normal, normal.answers[0].outputs["value"].0),
            &Scalar::Bool(true)
        );
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        let domain = in_domain(&normal, 0);
        assert!(
            matches!(&normal.nodes[domain].payload,Some(Payload::Domain {elements,..}) if elements.len()==2)
        );
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..=domain]).unwrap();
        rebuild_for_origin_and_support_recheck(
            &normal,
            &normal.nodes[..=normal.answers[0].outputs["value"].0],
        )
        .unwrap();
        for (name, original) in [
            ("owned", "forall r:E[root] . true"),
            (
                "nested_owned",
                "exists packed:(Unit,Option<Set<E[root]>>) . false",
            ),
        ] {
            let ask = format!("bad=evaluate(Calc.{name},root=@v/root)");
            let result =
                evaluate_observed_bytes(sources.clone(), &[&ask], &mut named_call_quiet()).unwrap();
            owned_type_private_completed_missing(&result, &law, original);
        }
    }
    #[test]
    fn plain_ref_exhaustion_rechecks_complete_coverage_and_accepts_set_presentations() {
        let result = plain_ref_example(&[
            "all=evaluate(Calc.all)",
            "sets=evaluate(Calc.powers)",
            "empty=evaluate(Calc.voidproduct)",
        ]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let proof = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (result.contexts[index].request == 0
                    && matches!(&node.payload, Some(Payload::FiniteExhaustion { .. })))
                .then_some(index)
            })
            .unwrap();
        let Some(Payload::FiniteExhaustion { instances, .. }) = &result.nodes[proof].payload else {
            unreachable!()
        };
        let bodies = instances.clone();
        assert_eq!(bodies.len(), 2);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=proof]).unwrap();
        for mutation in 0..6 {
            let mut changed = result.nodes[..=proof].to_vec();
            match mutation {
                0 => {
                    let Some(Payload::FiniteExhaustion { checked, .. }) =
                        &mut changed[proof].payload
                    else {
                        unreachable!()
                    };
                    *checked = 1;
                }
                1 => {
                    finite_instances(&mut changed, proof, vec![bodies[0]]);
                    let Some(Payload::FiniteExhaustion { checked, .. }) =
                        &mut changed[proof].payload
                    else {
                        unreachable!()
                    };
                    *checked = 1;
                }
                2 => finite_instances(&mut changed, proof, vec![bodies[0], bodies[0]]),
                3 => changed[proof].scope.quantifiers[0].kind = crate::law::ast::QuantKind::Exists,
                4 => {
                    changed[proof].scope.modes.remove("observed");
                }
                _ => {
                    changed[proof].support.clear();
                }
            }
            rejects_named_prefix(&result, &changed);
        }
        let Some(Payload::Evaluation {
            value: Some(value), ..
        }) = &result.nodes[bodies[0].0].payload
        else {
            unreachable!()
        };
        let value = value.0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=value]).unwrap();
        let mut changed = result.nodes[..=value].to_vec();
        changed[value].payload = Some(Payload::Scalar(Scalar::Bool(false)));
        rejects_named_prefix(&result, &changed);
        let value = result.answers[0].outputs["value"].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=value]).unwrap();
        let mut changed = result.nodes[..=value].to_vec();
        changed[value].evidence.clear();
        rejects_named_prefix(&result, &changed);
        let mut reordered = result.nodes.clone();
        let mut reverse = bodies;
        reverse.reverse();
        finite_instances(&mut reordered, proof, reverse);
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        let domain = in_domain(&result, 0);
        let mut reordered = result.nodes.clone();
        let Some(Payload::Domain { elements, .. }) = &mut reordered[domain].payload else {
            unreachable!()
        };
        elements.reverse();
        let refs = elements.clone();
        reordered[domain].arguments.truncate(1);
        reordered[domain].arguments.extend(refs);
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        let set=result.nodes.iter().enumerate().find_map(|(index,node)|(result.contexts[index].request==1 && matches!(&node.payload,Some(Payload::Scalar(Scalar::Set {items,..})) if items.len()==2)).then_some(index)).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=set]).unwrap();
        let mut reordered = result.nodes.clone();
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut reordered[set].payload else {
            unreachable!()
        };
        items.reverse();
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
    }
    #[test]
    fn plain_ref_counterexamples_reject_foreign_request_and_call_producers() {
        plain_ref_counterexample_producers(false);
    }
    #[test]
    fn plain_ref_counterexamples_reject_same_request_call_producers() {
        plain_ref_counterexample_producers(true);
    }
    fn plain_ref_counterexample_producers(same_request: bool) {
        let asks = if same_request {
            vec!["both=check(Calc.both)"]
        } else {
            vec!["first=check(Calc.called)", "again=check(Calc.called)"]
        };
        let result = plain_ref_example(&asks);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert!(
            result
                .answers
                .iter()
                .all(|answer| answer.status == Decision::Refuted)
        );
        let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let counters: Vec<_> = result
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                (result.contexts[index].case.is_none()
                    && node.arguments.len() == 3
                    && matches!(&node.payload, Some(Payload::Counterexample { .. })))
                .then_some(index)
            })
            .collect();
        assert_eq!(counters.len(), 2);
        for &counter in &counters {
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=counter]).unwrap();
            let Some(Payload::Counterexample {
                bindings,
                left,
                right,
                facts,
            }) = &result.nodes[counter].payload
            else {
                unreachable!()
            };
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].name, "r");
            assert_eq!(
                data_scalar_at(&result, bindings[0].value.0),
                &Scalar::Subject {
                    snapshot: "w".into(),
                    subject: "item".into(),
                    entity: "Roster.E".into()
                }
            );
            assert_eq!(data_scalar_at(&result, left.0), &Scalar::Bool(false));
            assert_eq!(data_scalar_at(&result, right.0), &Scalar::Bool(true));
            assert!(
                facts
                    .iter()
                    .any(|f| f.snapshot == "v" && f.subject == "item" && f.field.is_none())
            );
            assert!(
                facts
                    .iter()
                    .any(|f| f.snapshot == "w" && f.atom.as_deref() == Some("flag"))
            );
            let body = result.nodes[counter].arguments[2];
            assert!(result.nodes[body.0].scope.snapshots.contains("z"));
            assert!(
                result.answers[result.contexts[counter].request]
                    .reasons
                    .iter()
                    .any(
                        |reason| reason.missing.iter().any(|fact| fact.snapshot == "v"
                            && fact.subject == "item"
                            && fact.field.as_deref() == Some("Roster.E.flag"))
                    )
            );
        }
        // 補完後も二つのwhole評価がfalseであり、観測済wの反例が各caseへ実到達する。
        for (request, answer) in result.answers.iter().enumerate() {
            let evaluation = &result.nodes[answer.outputs["evaluation"].0];
            assert!(matches!(
                &result.nodes[evaluation.arguments[0].0].payload,
                Some(Payload::CompletionSeed { .. })
            ));
            let Some(Payload::Evaluation {
                parts,
                value: Some(value),
                ..
            }) = &evaluation.payload
            else {
                unreachable!()
            };
            assert_eq!(data_scalar_at(&result, value.0), &Scalar::Bool(false));
            let cases = &parts[0].children;
            assert_eq!(cases.len(), 2);
            assert!(answer.evidence.iter().any(|r|matches!(&result.nodes[r.0].payload,Some(Payload::FiniteExhaustion {checked:2,instances,..}) if instances.len()==cases.len() && instances.iter().all(|instance|cases.contains(instance)))));
            for &case in cases {
                let context = result.contexts[case.0];
                assert_eq!(context.request, request);
                assert!(
                    context.case.is_some()
                        && context.frame.is_none()
                        && context.instance.is_none()
                        && context.iteration.is_none()
                );
                assert!(
                    matches!(&result.nodes[case.0].payload,Some(Payload::Evaluation {value:Some(value),..}) if data_scalar_at(&result,value.0)==&Scalar::Bool(false))
                );
                let known=result.nodes.iter().enumerate().filter(|(i,node)| {
                    result.contexts[*i].request==request && result.contexts[*i].case==context.case
                        && node.arguments.len()==3
                        && matches!(&node.payload,Some(Payload::Counterexample {bindings,..}) if bindings.len()==1 && bindings[0].name=="r" && matches!(data_scalar_at(&result,bindings[0].value.0),Scalar::Subject {snapshot,subject,entity} if snapshot=="w" && subject=="item" && entity=="Roster.E"))
                        && graph.evaluation_evidence_contains(case,NodeRef(*i)).unwrap()
                }).count();
                assert_eq!(known, if same_request { 2 } else { 1 });
            }
        }
        {
            let (foreign, target) = (counters[0], counters[1]);
            assert_ne!(
                result.contexts[foreign].frame,
                result.contexts[target].frame
            );
            assert_eq!(
                result.contexts[foreign].request == result.contexts[target].request,
                same_request
            );
            let Some(Payload::Counterexample {
                bindings: other,
                left: other_left,
                right: other_right,
                ..
            }) = &result.nodes[foreign].payload
            else {
                unreachable!()
            };
            for mutation in 0..5 {
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
                    0 => bindings[0].value = other[0].value,
                    1 => *left = *other_left,
                    2 => *right = *other_right,
                    _ => {}
                }
                if mutation == 3 {
                    changed[target].arguments = result.nodes[foreign].arguments.clone();
                    changed[target].payload = result.nodes[foreign].payload.clone();
                    changed[target].scope = result.nodes[foreign].scope.clone();
                }
                if mutation == 4 {
                    changed[target].support.clear();
                    if let Some(Payload::Counterexample { facts, .. }) =
                        &mut changed[target].payload
                    {
                        facts.clear();
                    }
                }
                rejects_named_prefix(&result, &changed);
            }
        }
    }
    fn type_quantifier_fixture(omitted: &[&str]) -> InputSources {
        numeric_recheck_fixture(
            omitted,
            r#"
 view all(): Bool = forall bit: Bool . bit=bit;
 view unused(): Bool = forall item: Option<Bool> . true;
 view powers(): Bool = forall bag: Set<Bool> . count(bag)<=2;
 view negative(s: Sample): Bool = forall bit: Bool . bit or s.p;
 law required called(x: Sample): negative(x);
 law required both(x: Sample): negative(x) and negative(x);
 view nested(): Bool = let flag=true in forall singleton: Unit . exists bit in list<Bool>[flag] . match bit { held => exists option: Option<Bool> . held and option=option; };
 view observe(s: Sample): Q = s.q;
 view full(): Bool = forall bit: Bool . true;
 view early(): Bool = forall bit: Bool . bit;
 view later(): Z = 9;
"#,
        )
    }
    fn type_quantifier_example(requests: &[&str]) -> ObservedEvaluation {
        evaluate_observed_bytes(
            type_quantifier_fixture(&[]),
            requests,
            &mut named_call_quiet(),
        )
        .unwrap()
    }
    #[test]
    fn type_quantifier_prefixes_recheck_original_type_domain_members_scope_and_support() {
        let result = type_quantifier_example(&[
            "first=evaluate(Calc.all)",
            "again=evaluate(Calc.all)",
            "unused=evaluate(Calc.unused)",
            "powers=evaluate(Calc.powers)",
        ]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        for (request, count, ty) in [
            (0, 2, Type::Bool),
            (2, 3, Type::Option(Box::new(Type::Bool))),
            (3, 4, Type::Set(Box::new(Type::Bool))),
        ] {
            let domain = in_domain(&result, request);
            let Some(Payload::Domain {
                ty: actual,
                elements,
            }) = &result.nodes[domain].payload
            else {
                unreachable!()
            };
            assert_eq!(actual, &ty);
            assert_eq!(elements.len(), count);
            assert_eq!(result.nodes[domain].arguments.len(), 1 + count);
            let source = result.nodes[domain].arguments[0];
            let Some(Payload::Expression {
                location: Location::Law { span },
                parameters,
                ..
            }) = &result.nodes[source.0].payload
            else {
                unreachable!()
            };
            assert!(parameters.is_empty());
            let id = result
                .prepared
                .inputs()
                .law()
                .exprs
                .iter()
                .enumerate()
                .find_map(|(id, e)| {
                    (e.span == *span && result.prepared.inputs().law().expr_type(id).is_some())
                        .then_some(id)
                })
                .unwrap();
            assert_eq!(
                result.prepared.inputs().law().quantifier_types[id].as_ref(),
                Some(&ty)
            );
            for element in elements {
                assert_eq!(result.nodes[element.0].arguments, vec![source]);
            }
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=domain]).unwrap();
        }
        let domain = in_domain(&result, 0);
        let Some(Payload::Domain { elements, .. }) = &result.nodes[domain].payload else {
            unreachable!()
        };
        let member = elements[0].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=member]).unwrap();
        let mut changed = result.nodes[..=member].to_vec();
        changed[member].payload = Some(Payload::Scalar(Scalar::Z(0.into())));
        changed[member].ty = NodeType::Value(Type::Z);
        rejects_named_prefix(&result, &changed);
        for mutation in 0..3 {
            let mut changed = result.nodes[..=domain].to_vec();
            let Some(Payload::Domain { ty, elements }) = &mut changed[domain].payload else {
                unreachable!()
            };
            match mutation {
                0 => *ty = Type::Unit,
                1 => {
                    elements.pop();
                }
                _ => {
                    elements[1] = elements[0];
                }
            }
            let members = elements.clone();
            changed[domain].arguments.truncate(1);
            changed[domain].arguments.extend(members);
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
        changed[scalar].arguments[0] = NodeRef(domain);
        changed[scalar].scope.quantifiers[0].domain = Some(NodeRef(domain));
        rejects_named_prefix(&result, &changed);
        for mutation in 0..2 {
            let mut changed = result.nodes[..=scalar].to_vec();
            if mutation == 0 {
                changed[scalar].scope.completions = true;
            } else {
                changed[scalar].support.push(Fact {
                    snapshot: "v".into(),
                    subject: "sample".into(),
                    field: Some("Numeric.Sample.p".into()),
                    atom: Some("p".into()),
                });
            }
            rejects_named_prefix(&result, &changed);
        }
    }
    #[test]
    fn type_quantifier_exhaustion_rechecks_coverage_binder_body_and_evidence() {
        let mut result = type_quantifier_example(&[
            "full=evaluate(Calc.all)",
            "powers=evaluate(Calc.powers)",
            "nested=evaluate(Calc.nested)",
        ]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let proof = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (result.contexts[index].request == 0
                    && matches!(&node.payload, Some(Payload::FiniteExhaustion { .. })))
                .then_some(index)
            })
            .unwrap();
        let Some(Payload::FiniteExhaustion { instances, .. }) = &result.nodes[proof].payload else {
            unreachable!()
        };
        let bodies = instances.clone();
        assert_eq!(bodies.len(), 2);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=proof]).unwrap();
        for mutation in 0..4 {
            let mut changed = result.nodes[..=proof].to_vec();
            match mutation {
                0 => {
                    if let Some(Payload::FiniteExhaustion { checked, .. }) =
                        &mut changed[proof].payload
                    {
                        *checked = 1;
                    }
                }
                1 => finite_instances(&mut changed, proof, vec![bodies[0]]),
                2 => finite_instances(&mut changed, proof, vec![bodies[0], bodies[0]]),
                _ => changed[proof].scope.quantifiers[0].kind = crate::law::ast::QuantKind::Exists,
            }
            rejects_named_prefix(&result, &changed);
        }
        let binder = iteration_binder_scalar_for_name(&result, 0, b"bit");
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=binder]).unwrap();
        let old = result.iterations[0].member.clone();
        result.iterations[0].member = super::super::call::Member::SetElement(Scalar::Bool(true));
        rejects_named_prefix(&result, &result.nodes[..=binder]);
        result.iterations[0].member = old;
        let Some(Payload::Evaluation {
            value: Some(body_value),
            ..
        }) = &result.nodes[bodies[0].0].payload
        else {
            unreachable!()
        };
        let body_value = body_value.0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=body_value]).unwrap();
        let mut changed = result.nodes[..=body_value].to_vec();
        changed[body_value].payload = Some(Payload::Scalar(Scalar::Bool(false)));
        rejects_named_prefix(&result, &changed);
        let scalar = result.answers[0].outputs["value"].0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
        let mut changed = result.nodes[..=scalar].to_vec();
        changed[scalar].evidence.clear();
        rejects_named_prefix(&result, &changed);
        let mut reordered = result.nodes.clone();
        let mut reverse = bodies;
        reverse.reverse();
        finite_instances(&mut reordered, proof, reverse);
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        let domain = in_domain(&result, 1);
        let mut reordered = result.nodes.clone();
        let Some(Payload::Domain { elements, .. }) = &mut reordered[domain].payload else {
            unreachable!()
        };
        elements.reverse();
        let reverse = elements.clone();
        reordered[domain].arguments.truncate(1);
        reordered[domain].arguments.extend(reverse);
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        let set=result.nodes.iter().enumerate().find_map(|(index,node)|(result.contexts[index].request==1 && matches!(&node.payload,Some(Payload::Scalar(Scalar::Set {items,..})) if items.len()==2)).then_some(index)).unwrap();
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=set]).unwrap();
        let mut reordered = result.nodes.clone();
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut reordered[set].payload else {
            unreachable!()
        };
        items.reverse();
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
    }
    #[test]
    fn type_quantifier_call_capture_keeps_original_alias_producers() {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(
                &[],
                r#"
 view assess(b: Bool,s: Sample): Bool = let kept=b in match kept { p => (p or not p) and s.q<0; };
 view mixed(s: Sample): Bool = forall x:Bool . exists n in list<Z>[0] . assess(x or not x,s);
"#,
            ),
            &[
                "first=evaluate(Calc.mixed,s=@v/sample)",
                "again=evaluate(Calc.mixed,s=@v/sample)",
            ],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        for answer in &result.answers {
            assert_eq!(
                data_scalar_at(&result, answer.outputs["value"].0),
                &Scalar::Bool(true)
            );
        }
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let aliases: Vec<_> = result
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                let Some(Payload::Evaluation {
                    expression,
                    value: Some(value),
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
                (result.contexts[index].frame.is_some()
                    && &result.prepared.inputs().sources().law().bytes()[span.0..span.1] == b"b")
                    .then_some((index, *value))
            })
            .collect();
        assert_eq!(aliases.len(), 4);
        for (foreign, target) in [(aliases[0], aliases[1]), (aliases[1], aliases[2])] {
            assert_ne!(foreign.1, target.1);
            assert_eq!(
                result.contexts[foreign.0].request == result.contexts[target.0].request,
                foreign == aliases[0]
            );
            assert_eq!(
                data_scalar_at(&result, foreign.1.0),
                data_scalar_at(&result, target.1.0)
            );
            assert_ne!(
                result.contexts[foreign.0].frame,
                result.contexts[target.0].frame
            );
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target.1.0]).unwrap();
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target.0]).unwrap();
            let Some(Payload::Evaluation {
                parts: foreign_parts,
                ..
            }) = &result.nodes[foreign.0].payload
            else {
                unreachable!()
            };
            for change_child in [false, true] {
                let mut changed = result.nodes[..=target.0].to_vec();
                let Some(Payload::Evaluation {
                    expression,
                    parts,
                    value,
                    ..
                }) = &mut changed[target.0].payload
                else {
                    unreachable!()
                };
                *value = Some(foreign.1);
                parts[0].value = Some(foreign.1);
                if change_child {
                    parts[0].children = foreign_parts[0].children.clone();
                }
                let arguments = std::iter::once(*expression)
                    .chain(parts[0].children.iter().copied())
                    .chain(*value)
                    .collect();
                changed[target.0].arguments = arguments;
                rejects_named_prefix(&result, &changed);
            }
        }
    }
    #[test]
    fn type_quantifier_counterexamples_reject_foreign_request_and_call_producers() {
        let result = type_quantifier_example(&[
            "first=check(Calc.called,x=@v/sample)",
            "again=check(Calc.called,x=@v/sample)",
            "both=check(Calc.both,x=@v/sample)",
        ]);
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert!(result.answers.iter().all(|a| a.status == Decision::Refuted));
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
        for &counter in &counters {
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=counter]).unwrap();
            let Some(Payload::Counterexample {
                bindings,
                left,
                right,
                ..
            }) = &result.nodes[counter].payload
            else {
                unreachable!()
            };
            assert_eq!(
                bindings.iter().map(|b| b.name.as_str()).collect::<Vec<_>>(),
                vec!["s", "bit"]
            );
            assert_eq!(
                data_scalar_at(&result, bindings[1].value.0),
                &Scalar::Bool(false)
            );
            assert_eq!(data_scalar_at(&result, left.0), &Scalar::Bool(false));
            assert_eq!(data_scalar_at(&result, right.0), &Scalar::Bool(true));
        }
        for (foreign, target) in [(counters[0], counters[1]), (counters[2], counters[3])] {
            assert_ne!(
                result.contexts[foreign].frame,
                result.contexts[target].frame
            );
            assert_eq!(
                result.contexts[foreign].request == result.contexts[target].request,
                foreign == counters[2]
            );
            let Some(Payload::Counterexample {
                bindings: other,
                left: other_left,
                right: other_right,
                ..
            }) = &result.nodes[foreign].payload
            else {
                unreachable!()
            };
            for mutation in 0..4 {
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
                    0 => bindings[1].value = other[1].value,
                    1 => *left = *other_left,
                    2 => *right = *other_right,
                    _ => {}
                }
                if mutation == 3 {
                    changed[target].arguments = result.nodes[foreign].arguments.clone();
                    changed[target].payload = result.nodes[foreign].payload.clone();
                    changed[target].scope = result.nodes[foreign].scope.clone();
                }
                rejects_named_prefix(&result, &changed);
            }
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
        quantifier_actual_phases_preserve_stops(false, false);
    }
    #[test]
    fn type_quantifier_actual_enumeration_body_and_exhaustion_phases_preserve_stops() {
        quantifier_actual_phases_preserve_stops(true, false);
    }
    #[test]
    fn plain_ref_actual_roster_construction_domain_and_recheck_stops() {
        quantifier_actual_phases_preserve_stops(true, true);
    }
    fn finite_completion_fixture(body: &str, missing_q: bool) -> InputSources {
        let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"ClosedValue","version":"1","dependencies":[],"declarations":[
{"kind":"data","name":"ClosedValue.D","meaning":"有限の構造値。","constructors":[{"name":"Off","arguments":[],"meaning":"不活性。"},{"name":"On","arguments":["Bool"],"meaning":"真偽を持つ。"}]},
{"kind":"data","name":"ClosedValue.Twin","meaning":"別型の構造値。","constructors":[{"name":"Off","arguments":[],"meaning":"不活性。"},{"name":"On","arguments":["Bool"],"meaning":"真偽を持つ。"}]},
{"kind":"entity","name":"ClosedValue.Sample","meaning":"有限構造値を観測する対象。","parameters":[],"fields":[{"name":"u","type":"Unit","meaning":"単位。"},{"name":"t","type":["Tuple","Bool",["Fp","2"]],"meaning":"組。"},{"name":"o","type":["Option","Bool"],"meaning":"選択。"},{"name":"k","type":["Set","Bool"],"meaning":"集合。"},{"name":"d","type":["Data","ClosedValue.D"],"meaning":"構造値。"},{"name":"f","type":["Fp","2"],"meaning":"二元体。"},{"name":"q","type":"Q","meaning":"有理数。"}],"alignments":[]}]}]}"#;
        let checked =
            crate::definition::check_definitions(&[("definition0", definitions.as_bytes())])
                .unwrap();
        let digest = &checked.vocabularies["ClosedValue"].digest;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0"; reading Calc {{ use vocabulary ClosedValue version "1" digest "{digest}"; {body} }}"#
        );
        let atoms = if missing_q {
            ""
        } else {
            r#"{"id":"q","subject":"sample","field":"ClosedValue.Sample.q","value":["-2","3"],"origin":"values"}"#
        };
        let map = format!(
            r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"ClosedValue","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan","uri":"urn:fixture:closed-value","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{{"id":"base","mode":"observed","method":"対象を観測する。","locations":[{{"source":"scan","path":"state.model","span":[0,1]}}]}},{{"id":"values","mode":"observed","method":"有理数を観測する。","locations":[{{"source":"scan","path":"values.model","span":[2,3]}}]}}],"snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"ClosedValue.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
        );
        InputSources::from_bytes(
            vec![definitions.as_bytes().to_vec()],
            law.into_bytes(),
            map.into_bytes(),
        )
    }
    fn finite_completion_example(body: &str, asks: &[&str]) -> ObservedEvaluation {
        let result = evaluate_observed_bytes(
            finite_completion_fixture(body, false),
            asks,
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_ne!(result.status(), "error", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        result
    }
    fn finite_completion_domain(
        result: &ObservedEvaluation,
        answer: usize,
        count: usize,
        ty: Type,
    ) -> (usize, usize, Vec<NodeRef>) {
        let root = result.answers[answer].outputs["evaluation"].0;
        let domain = result.nodes[root].arguments[1].0;
        let Some(Payload::Domain {
            ty: actual,
            elements,
        }) = &result.nodes[domain].payload
        else {
            unreachable!()
        };
        assert_eq!(actual, &ty);
        assert_eq!(elements.len(), count);
        assert_eq!(result.nodes[domain].arguments[1..], *elements);
        (root, domain, elements.clone())
    }
    fn finite_completion_field_scalars(result: &ObservedEvaluation, bytes: &[u8]) -> Vec<usize> {
        let law = result.prepared.inputs().sources().law().bytes();
        result.nodes.iter().enumerate().filter_map(|(index,node)| {
            (result.contexts[index].case.is_some() && node.arguments.len()==3
                && matches!(&node.payload,Some(Payload::Scalar(_)))
                && matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span}} if &law[span.0..span.1]==bytes)).then_some(index)
        }).collect()
    }
    fn replace_completion_scalar(nodes: &mut [Node], target: usize, value: Scalar) {
        nodes[target].ty = NodeType::Value(value.ty());
        nodes[target].payload = Some(Payload::Scalar(value));
    }
    #[test]
    fn finite_completion_unit_keeps_one_member_missing_and_typed_projection() {
        let result = finite_completion_example(
            "view read(s:Sample):Unit=s.u;",
            &["first=evaluate(Calc.read,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        let (_, _, members) = finite_completion_domain(&result, 0, 1, Type::Unit);
        assert_eq!(data_scalar_at(&result, members[0].0), &Scalar::Unit);
        let answer = &result.answers[0];
        assert_eq!(
            data_scalar_at(&result, answer.outputs["value"].0),
            &Scalar::Unit
        );
        assert!(
            answer
                .reasons
                .iter()
                .flat_map(|r| &r.missing)
                .any(|fact| fact.field.as_deref() == Some("ClosedValue.Sample.u"))
        );
        assert!(answer.evidence.iter().any(|r|matches!(&result.nodes[r.0].payload,Some(Payload::FiniteExhaustion {checked:1,instances,..}) if instances.len()==1)));
        completion_mutation(&result, members[0].0, |nodes| {
            replace_completion_scalar(nodes, members[0].0, Scalar::Bool(false))
        });
        let fields = finite_completion_field_scalars(&result, b"s.u");
        assert_eq!(fields.len(), 1);
        let field = fields[0];
        let projection = result.nodes[field].arguments[2].0;
        completion_mutation(&result, projection, |nodes| {
            replace_completion_scalar(nodes, projection, Scalar::Bool(false))
        });
        completion_mutation(&result, field, |nodes| {
            replace_completion_scalar(nodes, field, Scalar::Bool(false))
        });
    }
    #[test]
    fn finite_completion_data_members_recheck_constructor_family_arity_and_payload() {
        let result = finite_completion_example(
            "view read(s:Sample):D=s.d;",
            &["first=evaluate(Calc.read,s=@v/sample)"],
        );
        assert_eq!(result.status(), "partial");
        let (_, _, members) =
            finite_completion_domain(&result, 0, 3, Type::Data("ClosedValue.D".into()));
        let member = members
            .iter()
            .find(|r| matches!(data_scalar_at(&result,r.0),Scalar::Data {args,..} if args.len()==1))
            .unwrap()
            .0;
        for variant in 0..4 {
            completion_mutation(&result, member, |nodes| {
                let Some(Payload::Scalar(Scalar::Data {
                    family,
                    constructor,
                    args,
                })) = &mut nodes[member].payload
                else {
                    unreachable!()
                };
                match variant {
                    0 => *constructor = "ClosedValue.D.Forged".into(),
                    1 => {
                        *family = "ClosedValue.Twin".into();
                        *constructor = "ClosedValue.Twin.On".into();
                        nodes[member].ty = NodeType::Value(Type::Data("ClosedValue.Twin".into()));
                    }
                    2 => args.clear(),
                    _ => args[0] = Scalar::Unit,
                }
            });
        }
        let fields = finite_completion_field_scalars(&result, b"s.d");
        assert_eq!(fields.len(), 3);
        let projection = result.nodes[fields[1]].arguments[2].0;
        completion_mutation(&result, projection, |nodes| {
            let Some(Payload::Scalar(Scalar::Data { constructor, .. })) =
                &mut nodes[projection].payload
            else {
                unreachable!()
            };
            *constructor = "ClosedValue.D.Forged".into();
        });
        completion_mutation(&result, fields[1], |nodes| {
            let Some(Payload::Scalar(Scalar::Data { args, .. })) = &mut nodes[fields[1]].payload
            else {
                unreachable!()
            };
            args.push(Scalar::Unit);
        });
        let pair = result.answers[0]
            .evidence
            .iter()
            .find(|r| {
                matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::CompletionPair { .. })
                )
            })
            .unwrap()
            .0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=pair]).unwrap();
    }
    #[test]
    fn finite_completion_tuple_field_is_one_slot_and_rechecks_nested_order() {
        let result = finite_completion_example(
            "view stable(s:Sample):Bool=(s.t.0,s.t.1)=s.t;",
            &["first=evaluate(Calc.stable,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        let (_, domain, members) = finite_completion_domain(
            &result,
            0,
            4,
            Type::Tuple(vec![Type::Bool, Type::Fp("2".into())]),
        );
        let seed = result.nodes[domain].arguments[0].0;
        assert!(
            matches!(&result.nodes[seed].payload,Some(Payload::CompletionSeed {fields,..}) if fields.len()==1 && fields[0].field.as_deref()==Some("ClosedValue.Sample.t"))
        );
        for variant in 0..3 {
            completion_mutation(&result, members[0].0, |nodes| {
                let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut nodes[members[0].0].payload
                else {
                    unreachable!()
                };
                match variant {
                    0 => items.swap(0, 1),
                    1 => items[0] = Scalar::Tuple(vec![items[0].clone(), Scalar::Unit]),
                    _ => items[1] = Scalar::Bool(false),
                }
            });
        }
        let fields = finite_completion_field_scalars(&result, b"s.t");
        assert_eq!(fields.len(), 12);
        let projection = result.nodes[fields[0]].arguments[2].0;
        completion_mutation(&result, projection, |nodes| {
            let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut nodes[projection].payload else {
                unreachable!()
            };
            items.swap(0, 1);
        });
        let source = result.nodes[fields[0]].arguments[0].0;
        completion_mutation(&result, source, |nodes| {
            let Some(Payload::Expression { bindings, .. }) = &mut nodes[source].payload else {
                unreachable!()
            };
            bindings[0].name = "foreign".into();
        });
    }
    #[test]
    fn finite_completion_option_members_keep_none_some_and_element_type() {
        let result = finite_completion_example(
            "view read(s:Sample):Option<Bool> = s.o;",
            &["first=evaluate(Calc.read,s=@v/sample)"],
        );
        assert_eq!(result.status(), "partial");
        let (_, domain, members) =
            finite_completion_domain(&result, 0, 3, Type::Option(Box::new(Type::Bool)));
        let none = members
            .iter()
            .find(|r| {
                matches!(
                    data_scalar_at(&result, r.0),
                    Scalar::Option { value: None, .. }
                )
            })
            .unwrap()
            .0;
        let some = members
            .iter()
            .find(|r| {
                matches!(
                    data_scalar_at(&result, r.0),
                    Scalar::Option { value: Some(_), .. }
                )
            })
            .unwrap()
            .0;
        completion_mutation(&result, none, |nodes| {
            replace_completion_scalar(
                nodes,
                none,
                Scalar::Option {
                    element: Type::Fp("2".into()),
                    value: None,
                },
            )
        });
        // member単独は型の任意の元を主張する。別の正当なtagへの変更は
        // 元Domainが主張する全域coverageとの不整合として照合する。
        completion_mutation(&result, domain, |nodes| {
            replace_completion_scalar(
                nodes,
                none,
                Scalar::Option {
                    element: Type::Bool,
                    value: Some(Box::new(Scalar::Bool(false))),
                },
            )
        });
        completion_mutation(&result, some, |nodes| {
            let Some(Payload::Scalar(Scalar::Option { value, .. })) = &mut nodes[some].payload
            else {
                unreachable!()
            };
            *value = Some(Box::new(Scalar::Unit));
        });
        let fields = finite_completion_field_scalars(&result, b"s.o");
        assert_eq!(fields.len(), 3);
        let projection = result.nodes[fields[0]].arguments[2].0;
        completion_mutation(&result, projection, |nodes| {
            replace_completion_scalar(
                nodes,
                projection,
                Scalar::Option {
                    element: Type::Bool,
                    value: Some(Box::new(Scalar::Bool(true))),
                },
            )
        });
    }
    #[test]
    fn finite_completion_set_members_reject_duplicates_and_accept_extensional_order() {
        let result = finite_completion_example(
            "view stable(s:Sample):Bool=count(s.k)>=0;",
            &["first=evaluate(Calc.stable,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        let (_, domain, members) =
            finite_completion_domain(&result, 0, 4, Type::Set(Box::new(Type::Bool)));
        let member = members
            .iter()
            .find(
                |r| matches!(data_scalar_at(&result,r.0),Scalar::Set {items,..} if items.len()==2),
            )
            .unwrap()
            .0;
        for variant in 0..3 {
            let target = if variant == 2 { domain } else { member };
            completion_mutation(&result, target, |nodes| {
                let Some(Payload::Scalar(Scalar::Set { element, items })) =
                    &mut nodes[member].payload
                else {
                    unreachable!()
                };
                match variant {
                    0 => items.push(items[0].clone()),
                    1 => *element = Type::Fp("2".into()),
                    _ => {
                        items.pop();
                    }
                }
            });
        }
        let fields = finite_completion_field_scalars(&result, b"s.k");
        assert_eq!(fields.len(), 4);
        let field = *fields
            .iter()
            .find(
                |i| matches!(data_scalar_at(&result,**i),Scalar::Set {items,..} if items.len()==2),
            )
            .unwrap();
        let projection = result.nodes[field].arguments[2].0;
        completion_mutation(&result, projection, |nodes| {
            let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut nodes[projection].payload
            else {
                unreachable!()
            };
            items.push(items[0].clone());
        });
        for target in [member, projection, field] {
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
            let mut reordered = result.nodes.clone();
            let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut reordered[target].payload
            else {
                unreachable!()
            };
            items.reverse();
            assert_ne!(
                format!("{:?}", reordered[target]),
                format!("{:?}", result.nodes[target])
            );
            rebuild_for_origin_and_support_recheck(&result, &reordered[..=target]).unwrap();
            rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        }
    }
    #[test]
    fn finite_completion_products_keep_outer_slot_tuple_and_six_assignments() {
        let result = finite_completion_example(
            "view mixed(s:Sample):(Option<Bool>,Fp(2))=(s.o,s.f);",
            &["first=evaluate(Calc.mixed,s=@v/sample)"],
        );
        assert_eq!(result.status(), "partial");
        let (_, domain, members) = finite_completion_domain(
            &result,
            0,
            6,
            Type::Tuple(vec![
                Type::Fp("2".into()),
                Type::Option(Box::new(Type::Bool)),
            ]),
        );
        let seed = result.nodes[domain].arguments[0].0;
        assert!(
            matches!(&result.nodes[seed].payload,Some(Payload::CompletionSeed {fields,..}) if fields.len()==2 && fields[0].field.as_deref()==Some("ClosedValue.Sample.f") && fields[1].field.as_deref()==Some("ClosedValue.Sample.o"))
        );
        completion_mutation(&result, members[0].0, |nodes| {
            let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut nodes[members[0].0].payload
            else {
                unreachable!()
            };
            items.swap(0, 1);
        });
        for variant in 0..3 {
            completion_mutation(&result, domain, |nodes| {
                let Some(Payload::Domain { ty, elements }) = &mut nodes[domain].payload else {
                    unreachable!()
                };
                match variant {
                    0 => {
                        *ty = Type::Tuple(vec![
                            Type::Option(Box::new(Type::Bool)),
                            Type::Fp("2".into()),
                        ])
                    }
                    1 => {
                        elements.pop();
                        nodes[domain].arguments.pop();
                    }
                    _ => {
                        elements[1] = elements[0];
                        nodes[domain].arguments[2] = nodes[domain].arguments[1];
                    }
                }
            });
        }
        completion_mutation(&result, seed, |nodes| {
            let Some(Payload::CompletionSeed {
                fields, sources, ..
            }) = &mut nodes[seed].payload
            else {
                unreachable!()
            };
            fields.swap(0, 1);
            sources.swap(0, 1);
            let len = nodes[seed].arguments.len();
            nodes[seed].arguments.swap(len - 2, len - 1);
        });
    }
    #[test]
    fn finite_completion_unit_prefixes_reject_foreign_call_and_request_owners() {
        let result = finite_completion_example(
            "view read(x:Sample):Unit=x.u; view paired(s:Sample,t:Sample):Bool=read(s)=read(t);",
            &[
                "first=evaluate(Calc.paired,s=@v/sample,t=@v/sample)",
                "again=evaluate(Calc.paired,s=@v/sample,t=@v/sample)",
            ],
        );
        assert_eq!(result.status(), "complete");
        let fields = finite_completion_field_scalars(&result, b"x.u");
        assert_eq!(fields.len(), 4);
        assert_eq!(
            result.contexts[fields[0]].request,
            result.contexts[fields[1]].request
        );
        assert_ne!(
            result.contexts[fields[0]].frame,
            result.contexts[fields[1]].frame
        );
        assert_ne!(
            result.contexts[fields[0]].request,
            result.contexts[fields[2]].request
        );
        for target in [fields[1], fields[2]] {
            let foreign = result.nodes[fields[0]].arguments[1];
            let own = result.nodes[target].arguments[1];
            assert_ne!(foreign, own);
            assert_eq!(
                data_scalar_at(&result, foreign.0),
                data_scalar_at(&result, own.0)
            );
            completion_mutation(&result, target, |nodes| {
                nodes[target].arguments[1] = foreign
            });
        }
        completion_mutation(&result, fields[1], |nodes| {
            nodes[fields[1]].arguments[0] = result.nodes[fields[0]].arguments[0]
        });
        let source = result.nodes[fields[1]].arguments[0].0;
        completion_mutation(&result, source, |nodes| {
            let Some(Payload::Expression { bindings, .. }) = &mut nodes[source].payload else {
                unreachable!()
            };
            bindings[0].name = "foreign".into();
        });
        let Signature::View { body, .. } =
            &result.prepared.inputs().law().declarations["Calc.paired"].signature
        else {
            unreachable!()
        };
        let span = result.prepared.inputs().law().exprs[*body].span;
        completion_mutation(&result, fields[1], |nodes| {
            nodes[fields[1]].rule = Rule::Input {
                kind: "law",
                location: Location::Law { span },
            }
        });
    }
    #[test]
    fn finite_completion_unit_families_reject_same_case_foreign_instance_sources() {
        let result = finite_completion_example(
            "law required related(s:Sample,b:Bool):b=(s.u=s.u);",
            &["family=check(Calc.related,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        assert_eq!(result.answers[0].status, Decision::Refuted);
        let fields = finite_completion_field_scalars(&result, b"s.u");
        assert_eq!(fields.len(), 4);
        assert_eq!(
            result.contexts[fields[0]].case,
            result.contexts[fields[2]].case
        );
        assert_ne!(
            result.contexts[fields[0]].instance,
            result.contexts[fields[2]].instance
        );
        assert_eq!(
            data_scalar_at(&result, fields[0]),
            data_scalar_at(&result, fields[2])
        );
        completion_mutation(&result, fields[2], |nodes| {
            nodes[fields[2]].arguments[0] = result.nodes[fields[0]].arguments[0]
        });
        // 固定sは元rootの同じproducerを正当に共有する。instance固有なのは
        // fieldの実Source出現であり、共有owner Refの差を要求しない。
        assert_eq!(
            result.nodes[fields[0]].arguments[1],
            result.nodes[fields[2]].arguments[1]
        );
    }
    #[test]
    fn finite_completion_data_families_check_all_rows_before_case_coverage() {
        finite_completion_data_family_example();
    }
    fn finite_completion_data_family_example() -> (ObservedEvaluation, usize) {
        let result = finite_completion_example(
            "law required related(s:Sample,b:D):b=s.d;",
            &["family=check(Calc.related,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        assert_eq!(result.answers[0].status, Decision::Refuted);
        let proof = result.answers[0]
            .evidence
            .iter()
            .find(|r| {
                matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::FiniteExhaustion { .. })
                )
            })
            .unwrap()
            .0;
        let Some(Payload::FiniteExhaustion {
            instances, checked, ..
        }) = &result.nodes[proof].payload
        else {
            unreachable!()
        };
        assert_eq!(*checked, 3);
        assert_eq!(instances.len(), 3);
        for &case in instances {
            let context = result.contexts[case.0];
            let record = &result.cases[context.case.unwrap()];
            let assignment = data_scalar_at(&result, record.values[0].0);
            assert!(
                matches!(&result.nodes[case.0].payload,Some(Payload::Evaluation {value:Some(v),parts,..}) if data_scalar_at(&result,v.0)==&Scalar::Bool(false) && parts[0].children.len()==3)
            );
            assert!(result.nodes.iter().enumerate().any(|(i,node)|result.contexts[i].case==context.case && matches!(&node.payload,Some(Payload::Counterexample {bindings,..}) if bindings.iter().any(|b|b.name=="b" && data_scalar_at(&result,b.value.0)!=assignment))));
        }
        (result, proof)
    }
    #[test]
    fn finite_completion_data_family_rejects_wrong_case_count() {
        let (result, proof) = finite_completion_data_family_example();
        completion_mutation(&result, proof, |nodes| {
            let Some(Payload::FiniteExhaustion { checked, .. }) = &mut nodes[proof].payload else {
                unreachable!()
            };
            *checked += 1;
        });
    }
    #[test]
    fn finite_completion_data_family_rejects_duplicate_case_producer() {
        let (result, proof) = finite_completion_data_family_example();
        completion_mutation(&result, proof, |nodes| {
            let Some(Payload::FiniteExhaustion { instances, .. }) = &mut nodes[proof].payload
            else {
                unreachable!()
            };
            instances[1] = instances[0];
            nodes[proof].arguments[3] = nodes[proof].arguments[2];
        });
    }
    #[test]
    fn finite_completion_data_family_rejects_omitted_case_producer() {
        let (result, proof) = finite_completion_data_family_example();
        completion_mutation(&result, proof, |nodes| {
            let Some(Payload::FiniteExhaustion { instances, .. }) = &mut nodes[proof].payload
            else {
                unreachable!()
            };
            instances.pop();
            nodes[proof].arguments.pop();
        });
    }
    #[test]
    fn finite_completion_data_family_rejects_claim_decision_flip() {
        let (result, _) = finite_completion_data_family_example();
        let proposition = result.answers[0].claim.unwrap().0;
        completion_mutation(&result, proposition, |nodes| {
            nodes[proposition].judgment.as_mut().unwrap().status = Decision::Established
        });
    }
    #[test]
    fn finite_completion_option_pairs_recheck_assignment_types_and_case_results() {
        let result = finite_completion_example(
            "view read(s:Sample):Option<Bool> = s.o;",
            &["first=evaluate(Calc.read,s=@v/sample)"],
        );
        assert_eq!(result.status(), "partial");
        let pair = result.answers[0]
            .evidence
            .iter()
            .find(|r| {
                matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::CompletionPair { .. })
                )
            })
            .unwrap()
            .0;
        let root = result.answers[0].outputs["evaluation"].0;
        let seed = result.nodes[root].arguments[0];
        let third = result
            .cases
            .iter()
            .filter(|case| case.seed == seed)
            .nth(2)
            .unwrap()
            .values[0];
        for variant in 0..3 {
            completion_mutation(&result, pair, |nodes| {
                let Some(Payload::CompletionPair {
                    fields,
                    first,
                    first_result,
                    second_result,
                    ..
                }) = &mut nodes[pair].payload
                else {
                    unreachable!()
                };
                match variant {
                    0 => fields[0].field = Some("ClosedValue.Sample.u".into()),
                    1 => {
                        first[0] = third;
                        nodes[pair].arguments[4] = third;
                    }
                    _ => {
                        *second_result = *first_result;
                        nodes[pair].arguments[3] = nodes[pair].arguments[2];
                    }
                }
            });
        }
    }
    #[test]
    fn finite_completion_scope_support_case_producers_and_fresh_sessions_are_exact() {
        let result = finite_completion_example(
            "view stable(s:Sample):Bool=s.o=s.o;",
            &["first=evaluate(Calc.stable,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        let (root, domain, _) =
            finite_completion_domain(&result, 0, 3, Type::Option(Box::new(Type::Bool)));
        let scalar = result.answers[0].outputs["value"].0;
        let seed = result.nodes[domain].arguments[0].0;
        let proof = result.answers[0].evidence[0].0;
        let fact = result.nodes[scalar].support.first().unwrap().clone();
        for target in [seed, scalar, proof] {
            completion_mutation(&result, target, |nodes| {
                if nodes[target].support.is_empty() {
                    nodes[target].support.push(fact.clone());
                } else {
                    nodes[target].support.clear();
                }
            });
        }
        for target in [domain, scalar, root] {
            completion_mutation(&result, target, |nodes| {
                assert!(nodes[target].scope.snapshots.remove("v"))
            });
        }
        completion_mutation(&result, scalar, |nodes| {
            replace_completion_scalar(nodes, scalar, Scalar::Bool(false))
        });
        let fields = finite_completion_field_scalars(&result, b"s.o");
        assert_eq!(fields.len(), 6);
        assert_ne!(
            result.contexts[fields[0]].case,
            result.contexts[fields[2]].case
        );
        let foreign = result.nodes[fields[0]].arguments[1];
        let own = result.nodes[fields[2]].arguments[1];
        assert_ne!(foreign, own);
        assert_eq!(
            data_scalar_at(&result, foreign.0),
            data_scalar_at(&result, own.0)
        );
        completion_mutation(&result, fields[2], |nodes| {
            nodes[fields[2]].arguments[1] = foreign
        });
        let Signature::View { body, .. } =
            &result.prepared.inputs().law().declarations["Calc.stable"].signature
        else {
            unreachable!()
        };
        let span = result.prepared.inputs().law().exprs[*body].span;
        let roots:Vec<_>=result.nodes.iter().enumerate().filter_map(|(i,node)| {
            (result.contexts[i].case.is_some() && result.contexts[i].frame.is_none() && result.contexts[i].iteration.is_none() && result.contexts[i].instance.is_none()
                && matches!(&node.payload,Some(Payload::Evaluation {expression,..}) if matches!(&result.nodes[expression.0].payload,Some(Payload::Expression {location:Location::Law {span:actual},..}) if *actual==span))).then_some(i)
        }).collect();
        assert_eq!(roots.len(), 3);
        let value = |index: usize| {
            let Some(Payload::Evaluation {
                value: Some(value), ..
            }) = &result.nodes[index].payload
            else {
                unreachable!()
            };
            *value
        };
        let (foreign, own) = (value(roots[0]), value(roots[1]));
        assert_ne!(foreign, own);
        assert_eq!(
            data_scalar_at(&result, foreign.0),
            data_scalar_at(&result, own.0)
        );
        completion_mutation(&result, roots[1], |nodes| {
            let Some(Payload::Evaluation { value, parts, .. }) = &mut nodes[roots[1]].payload
            else {
                unreachable!()
            };
            *value = Some(foreign);
            parts[0].value = Some(foreign);
            for arg in &mut nodes[roots[1]].arguments {
                if *arg == own {
                    *arg = foreign;
                }
            }
        });
        let mut reordered = result.nodes.clone();
        let Some(Payload::Domain { elements, .. }) = &mut reordered[domain].payload else {
            unreachable!()
        };
        elements.reverse();
        reordered[domain].arguments[1..].reverse();
        let Some(Payload::FiniteExhaustion { instances, .. }) = &mut reordered[proof].payload
        else {
            unreachable!()
        };
        instances.reverse();
        reordered[proof].arguments[2..].reverse();
        let Some(Payload::Evaluation { parts, .. }) = &mut reordered[root].payload else {
            unreachable!()
        };
        parts[0].children.reverse();
        reordered[root].arguments[2..].reverse();
        reordered[scalar].arguments[2..].reverse();
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        let mut graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let mut control = named_call_quiet();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        environment
            .recheck_node(&graph, &graph.nodes[scalar], scalar)
            .unwrap();
        let original = graph.nodes[seed].scope.clone();
        assert!(graph.nodes[seed].scope.readings.insert("Foreign".into()));
        assert!(matches!(
            environment.recheck_node(&graph, &graph.nodes[scalar], scalar),
            Err(ValidationFailure::Internal(_))
        ));
        graph.nodes[seed].scope = original;
        environment
            .recheck_node(&graph, &graph.nodes[scalar], scalar)
            .unwrap();
    }
    #[test]
    fn finite_completion_enumeration_stop_keeps_original_prefixes() {
        finite_completion_phase_stop("completion_enum", 1, 0, None);
    }
    #[test]
    fn finite_completion_case_stop_keeps_completed_case_and_missing() {
        finite_completion_phase_stop("completion_case", 1, 1, None);
    }
    #[test]
    fn finite_completion_coverage_stop_keeps_all_cases_without_unfinished_proof() {
        finite_completion_phase_stop("completion_coverage", 0, 2, None);
    }
    #[test]
    fn finite_completion_enumeration_stop_keeps_verified_unit_value() {
        finite_completion_phase_stop("completion_enum", 1, 1, Some(false));
    }
    #[test]
    fn finite_completion_enumeration_stop_keeps_verified_law_counterexample() {
        finite_completion_phase_stop("completion_enum", 1, 2, Some(true));
    }
    fn finite_completion_phase_stop(
        phase: &'static str,
        at: usize,
        kind: usize,
        known: Option<bool>,
    ) {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{
            cell::{Cell, RefCell},
            rc::Rc,
        };
        let current = match known {
            Some(true) => "law required current(s:Sample):false and s.o=none<Bool>;",
            Some(false) => "view current(s:Sample):Unit=if s.o=none<Bool> then unit else unit;",
            None => "view current(s:Sample):Bool=s.o=s.o;",
        };
        let body = format!(
            "view seed():Unit=unit; law required prior(s:Sample):false; view hole(s:Sample):Q=s.q; {current}"
        );
        let inputs = finite_completion_fixture(&body, true);
        let ask = if known == Some(true) {
            "current=check(Calc.current,s=@v/sample)"
        } else {
            "current=evaluate(Calc.current,s=@v/sample)"
        };
        let asks = [
            "seed=evaluate(Calc.seed)",
            "prior=check(Calc.prior,s=@v/sample)",
            "hole=evaluate(Calc.hole,s=@v/sample)",
            ask,
            "later=evaluate(Calc.seed)",
        ];
        let mut quiet = named_call_quiet();
        let prepared = prepare_observed(inputs.clone(), &asks, &mut quiet).unwrap();
        let declaration = &prepared.inputs().law().declarations["Calc.current"];
        let target = declaration.span;
        let body_id = match &declaration.signature {
            Signature::View { body, .. } | Signature::Law { body, .. } => *body,
            _ => unreachable!(),
        };
        let body_span = prepared.inputs().law().exprs[body_id].span;
        let progress = Rc::new(RefCell::new(Vec::new()));
        let observed = progress.clone();
        let normal = evaluate_observed_with_validator(
            prepared,
            &mut quiet,
            |environment, graph, request, answer| {
                environment.validate_answer(graph, request, answer)?;
                if request.id == "hole" {
                    let observed = observed.clone();
                    data::observe_iterations(move |span, context, operation, index| {
                        if span == target
                            && context.request == 3
                            && context.case.is_none()
                            && operation == phase
                        {
                            observed.borrow_mut().push(index);
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
        assert!(normal.answers[1].evidence.iter().any(|r| matches!(
            &normal.nodes[r.0].payload,
            Some(Payload::Counterexample { .. })
        )));
        assert_eq!(
            normal.answers[3].status,
            if known == Some(true) {
                Decision::Refuted
            } else {
                Decision::Established
            }
        );
        assert_eq!(
            &*progress.borrow(),
            if phase == "completion_coverage" {
                &[0][..]
            } else {
                &[0, 1, 2][..]
            }
        );
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        let original = if let Some(check) = known {
            let roots:Vec<_>=normal.nodes.iter().enumerate().filter_map(|(index,node)| {
                let context=normal.contexts[index];
                (context.request==3 && context.case.is_none() && context.frame.is_none() && context.iteration.is_none() && context.instance.is_none()
                    && matches!(&node.payload,Some(Payload::Evaluation {expression,..}) if matches!(&normal.nodes[expression.0].payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==body_span))).then_some(NodeRef(index))
            }).collect();
            assert_eq!(roots.len(), 1);
            let root = roots[0];
            let Some(Payload::Evaluation {
                value: Some(value), ..
            }) = &normal.nodes[root.0].payload
            else {
                panic!("verified known observed root")
            };
            let value = *value;
            assert_eq!(
                data_scalar_at(&normal, value.0),
                &if check {
                    Scalar::Bool(false)
                } else {
                    Scalar::Unit
                }
            );
            rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..=value.0]).unwrap();
            let proposition = if check {
                let props: Vec<_> = normal
                    .nodes
                    .iter()
                    .enumerate()
                    .filter_map(|(i, node)| {
                        (normal.contexts[i].request == 3
                            && normal.contexts[i].case.is_none()
                            && matches!(&node.payload, Some(Payload::Proposition { .. }))
                            && node.arguments.get(1) == Some(&root))
                        .then_some(NodeRef(i))
                    })
                    .collect();
                assert_eq!(props.len(), 1);
                let reference = props[0];
                assert!(normal.nodes[reference.0].evidence.iter().any(|r| matches!(
                    &normal.nodes[r.0].payload,
                    Some(Payload::Counterexample { .. })
                )));
                rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..=reference.0])
                    .unwrap();
                Some(reference)
            } else {
                None
            };
            Some((root, value, proposition))
        } else {
            None
        };
        let (limits, usage, expected) = match kind {
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
        let prepared = prepare_observed(inputs, &asks, &mut control).unwrap();
        let seen = Rc::new(RefCell::new(Vec::new()));
        let observed = seen.clone();
        let stopped = evaluate_observed_with_validator(
            prepared,
            &mut control,
            |environment, graph, request, answer| {
                environment.validate_answer(graph, request, answer)?;
                if request.id == "hole" {
                    let (observed, armed) = (observed.clone(), armed.clone());
                    data::observe_iterations(move |span, context, operation, index| {
                        if span == target
                            && context.request == 3
                            && context.case.is_none()
                            && operation == phase
                        {
                            observed.borrow_mut().push(index);
                            if index == at {
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
        assert_eq!(seen.borrow().last(), Some(&at));
        assert_eq!(control.stop_reason(), Some(expected.clone()));
        assert_eq!(Some(probes.get()), frozen.get());
        assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
        let Json::Obj(ref normal_wire) = normal.wire() else {
            unreachable!()
        };
        let Json::Arr(normal_answers) = &normal_wire["answers"] else {
            unreachable!()
        };
        let Json::Obj(ref stopped_wire) = stopped.wire() else {
            unreachable!()
        };
        let Json::Arr(stopped_answers) = &stopped_wire["answers"] else {
            unreachable!()
        };
        assert_eq!(&stopped_answers[..3], &normal_answers[..3]);
        if let Some((root, value, proposition)) = original {
            assert_eq!(stopped.answers[3].status, normal.answers[3].status);
            assert_eq!(stopped.answers[3].outputs.get("evaluation"), Some(&root));
            assert_eq!(stopped.answers[3].claim, proposition);
            if let Some(proposition) = proposition {
                assert_eq!(
                    stopped.answers[3].evidence,
                    normal.nodes[proposition.0].evidence
                );
                assert!(stopped.answers[3].evidence.iter().any(|r| matches!(
                    &stopped.nodes[r.0].payload,
                    Some(Payload::Counterexample { .. })
                )));
            } else {
                assert_eq!(stopped.answers[3].outputs.get("value"), Some(&value));
            }
        } else {
            assert_eq!(stopped.answers[3].status, Decision::Undetermined);
            assert!(stopped.answers[3].outputs.is_empty());
            assert!(stopped.answers[3].evidence.is_empty());
        }
        assert!(
            stopped.answers[3]
                .reasons
                .iter()
                .flat_map(|reason| &reason.missing)
                .any(|fact| fact.field.as_deref() == Some("ClosedValue.Sample.o"))
        );
        assert_eq!(stopped.answers[4].status, Decision::Undetermined);
        assert!(stopped.answers[4].outputs.is_empty());
        for answer in &stopped.answers[3..] {
            let reason = answer
                .reasons
                .iter()
                .find(|r| matches!(&r.kind,ReasonKind::Stop(actual) if actual==&expected))
                .unwrap();
            let Json::Obj(ref wire) = reason.wire() else {
                unreachable!()
            };
            let Json::Obj(ref expected_wire) = expected.wire() else {
                unreachable!()
            };
            assert_eq!(wire.get("details"), expected_wire.get("details"));
        }
        let completed=stopped.nodes.iter().enumerate().filter(|(i,node)|stopped.contexts[*i].request==3 && stopped.contexts[*i].case.is_some() && stopped.contexts[*i].frame.is_none() && stopped.contexts[*i].iteration.is_none() && stopped.contexts[*i].instance.is_none()
            && matches!(&node.payload,Some(Payload::Evaluation {expression,..}) if matches!(&stopped.nodes[expression.0].payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==body_span))).count();
        assert_eq!(
            completed,
            if phase == "completion_enum" {
                0
            } else if phase == "completion_case" {
                1
            } else {
                3
            }
        );
        assert!(
            !stopped
                .nodes
                .iter()
                .enumerate()
                .any(|(i, node)| stopped.contexts[i].request == 3
                    && matches!(
                        &node.payload,
                        Some(Payload::FiniteExhaustion { .. } | Payload::CompletionPair { .. })
                    ))
        );
        rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
        let before = probes.get();
        assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
        assert_eq!(probes.get(), before);
    }
    #[test]
    fn finite_completion_recheck_entry_stops_keep_graph_and_original_reason() {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{cell::Cell, rc::Rc};
        let result = finite_completion_example(
            "view stable(s:Sample):Bool=s.o=s.o;",
            &["first=evaluate(Calc.stable,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        let scalar = result.answers[0].outputs["value"].0;
        let graph =
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
        let snapshot = || {
            format!(
                "{:?}",
                (
                    &graph.nodes,
                    &graph.contexts,
                    &graph.frames,
                    &graph.iterations,
                    &graph.instances,
                    &graph.cases
                )
            )
        };
        let before = snapshot();
        for kind in 0..3 {
            let (limits, usage, expected) = match kind {
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
            let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
            environment
                .recheck_node(&graph, &graph.nodes[scalar], scalar)
                .unwrap();
            let prior = probes.get();
            armed.set(true);
            let failure = environment
                .recheck_node(&graph, &graph.nodes[scalar], scalar)
                .unwrap_err();
            let ValidationFailure::Stop(actual) = failure else {
                panic!("有限構造値再照合のStopを保持する")
            };
            assert_eq!(actual, expected);
            assert_eq!(actual.wire(), expected.wire());
            assert_eq!(probes.get(), prior + 1);
            assert_eq!(Some(probes.get()), frozen.get());
            assert_eq!(snapshot(), before);
            assert!(
                matches!(environment.recheck_node(&graph,&graph.nodes[scalar],scalar),Err(ValidationFailure::Stop(actual)) if actual==expected)
            );
            assert_eq!(Some(probes.get()), frozen.get());
            assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
            assert_eq!(Some(probes.get()), frozen.get());
        }
        rebuild_for_origin_and_support_recheck(&result, &graph.nodes).unwrap();
    }
    fn fp_completion_fixture(body: &str, missing_q: bool) -> InputSources {
        let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"FiniteScalar","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"FiniteScalar.Sample","meaning":"有限原始値を観測する対象。","parameters":[],"fields":[{"name":"f","type":["Fp","2"],"meaning":"二元体。"},{"name":"g","type":["Fp","3"],"meaning":"三元体。"},{"name":"p","type":"Bool","meaning":"条件。"},{"name":"q","type":"Q","meaning":"有理数。"}],"alignments":[]}]}]}"#;
        let checked =
            crate::definition::check_definitions(&[("definition0", definitions.as_bytes())])
                .unwrap();
        let digest = &checked.vocabularies["FiniteScalar"].digest;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0"; reading Calc {{ use vocabulary FiniteScalar version "1" digest "{digest}"; {body} }}"#
        );
        let atoms = if missing_q {
            ""
        } else {
            r#"{"id":"q","subject":"sample","field":"FiniteScalar.Sample.q","value":["-2","3"],"origin":"values"}"#
        };
        let map = format!(
            r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"FiniteScalar","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan","uri":"urn:fixture:finite-scalar","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{{"id":"base","mode":"observed","method":"対象を観測する。","locations":[{{"source":"scan","path":"state.model","span":[0,1]}}]}},{{"id":"values","mode":"observed","method":"有理数を観測する。","locations":[{{"source":"scan","path":"values.model","span":[2,3]}}]}}],"snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"FiniteScalar.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
        );
        InputSources::from_bytes(
            vec![definitions.as_bytes().to_vec()],
            law.into_bytes(),
            map.into_bytes(),
        )
    }
    fn fp_completion_example(body: &str, asks: &[&str]) -> ObservedEvaluation {
        let result = evaluate_observed_bytes(
            fp_completion_fixture(body, false),
            asks,
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_ne!(result.status(), "error", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        result
    }
    fn fp_completion_field_scalars(result: &ObservedEvaluation, bytes: &[u8]) -> Vec<usize> {
        let law = result.prepared.inputs().sources().law().bytes();
        result.nodes.iter().enumerate().filter_map(|(index,node)| {
            (result.contexts[index].case.is_some() && node.arguments.len()==3
                && matches!(&node.payload,Some(Payload::Scalar(Scalar::Fp {..})))
                && matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span}} if &law[span.0..span.1]==bytes)).then_some(index)
        }).collect()
    }
    #[test]
    fn fp_completion_domains_recheck_moduli_members_and_projection_prefixes() {
        let result = fp_completion_example(
            "view stable(s:Sample):Fp(2)=s.f-s.f;",
            &["first=evaluate(Calc.stable,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        assert_eq!(
            data_scalar_at(&result, result.answers[0].outputs["value"].0),
            &Scalar::Fp {
                modulus: "2".into(),
                value: 0.into()
            }
        );
        let root = result.answers[0].outputs["evaluation"].0;
        let domain = result.nodes[root].arguments[1].0;
        let seed = result.nodes[domain].arguments[0].0;
        let Some(Payload::Domain { ty, elements }) = &result.nodes[domain].payload else {
            unreachable!()
        };
        assert_eq!(ty, &Type::Fp("2".into()));
        assert_eq!(elements.len(), 2);
        for variant in 0..4 {
            completion_mutation(&result, domain, |nodes| match variant {
                0 | 1 => {
                    let Some(Payload::Domain { ty, .. }) = &mut nodes[domain].payload else {
                        unreachable!()
                    };
                    *ty = if variant == 0 {
                        Type::Bool
                    } else {
                        Type::Fp("3".into())
                    };
                }
                2 => {
                    let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
                        unreachable!()
                    };
                    elements.pop();
                    nodes[domain].arguments.pop();
                }
                _ => {
                    let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
                        unreachable!()
                    };
                    elements[1] = elements[0];
                    nodes[domain].arguments[2] = nodes[domain].arguments[1];
                }
            });
        }
        let member = elements[0].0;
        completion_mutation(&result, member, |nodes| {
            nodes[member].payload = Some(Payload::Scalar(Scalar::Fp {
                modulus: "2".into(),
                value: 2.into(),
            }))
        });
        completion_mutation(&result, member, |nodes| {
            nodes[member].ty = NodeType::Value(Type::Bool);
            nodes[member].payload = Some(Payload::Scalar(Scalar::Bool(false)));
        });
        let fields = fp_completion_field_scalars(&result, b"s.f");
        assert_eq!(fields.len(), 4);
        let field = fields[0];
        let projection = result.nodes[field].arguments[2].0;
        for variant in 0..2 {
            completion_mutation(&result, projection, |nodes| {
                let ty = if variant == 0 {
                    Type::Bool
                } else {
                    Type::Fp("3".into())
                };
                nodes[projection].ty = NodeType::Value(ty);
                nodes[projection].payload = Some(Payload::Scalar(if variant == 0 {
                    Scalar::Bool(false)
                } else {
                    Scalar::Fp {
                        modulus: "3".into(),
                        value: 0.into(),
                    }
                }));
            });
        }
        completion_mutation(&result, seed, |nodes| {
            let Some(Payload::CompletionSeed { fields, .. }) = &mut nodes[seed].payload else {
                unreachable!()
            };
            fields[0].field = Some("FiniteScalar.Sample.g".into());
        });
        let source = result.nodes[field].arguments[0].0;
        completion_mutation(&result, source, |nodes| {
            let Some(Payload::Expression { bindings, .. }) = &mut nodes[source].payload else {
                unreachable!()
            };
            bindings[0].name = "foreign".into();
        });
        let Signature::View { body, .. } =
            &result.prepared.inputs().law().declarations["Calc.stable"].signature
        else {
            unreachable!()
        };
        let span = result.prepared.inputs().law().exprs[*body].span;
        completion_mutation(&result, field, |nodes| {
            nodes[field].rule = Rule::Input {
                kind: "law",
                location: Location::Law { span },
            }
        });
    }
    #[test]
    fn fp_completion_mixed_assignments_recheck_slot_order_and_original_types() {
        let result = fp_completion_example(
            "view mixed(s:Sample):(Fp(2),Bool)=(s.f,s.p);",
            &["first=evaluate(Calc.mixed,s=@v/sample)"],
        );
        assert_eq!(result.status(), "partial");
        assert_eq!(result.answers[0].status, Decision::Undetermined);
        let root = result.answers[0].outputs["evaluation"].0;
        let domain = result.nodes[root].arguments[1].0;
        let seed = result.nodes[domain].arguments[0].0;
        let Some(Payload::Domain { ty, elements }) = &result.nodes[domain].payload else {
            unreachable!()
        };
        assert_eq!(ty, &Type::Tuple(vec![Type::Fp("2".into()), Type::Bool]));
        assert_eq!(elements.len(), 4);
        let Some(Payload::CompletionSeed {
            fields, sources, ..
        }) = &result.nodes[seed].payload
        else {
            unreachable!()
        };
        assert_eq!(
            fields
                .iter()
                .map(|f| f.field.as_deref())
                .collect::<Vec<_>>(),
            vec![Some("FiniteScalar.Sample.f"), Some("FiniteScalar.Sample.p")]
        );
        let source_count = sources.len();
        completion_mutation(&result, domain, |nodes| {
            let Some(Payload::CompletionSeed {
                fields, sources, ..
            }) = &mut nodes[seed].payload
            else {
                unreachable!()
            };
            fields.swap(0, 1);
            sources.swap(0, 1);
            let n = nodes[seed].arguments.len();
            nodes[seed]
                .arguments
                .swap(n - source_count, n - source_count + 1);
        });
        completion_mutation(&result, domain, |nodes| {
            let swapped = Type::Tuple(vec![Type::Bool, Type::Fp("2".into())]);
            let Some(Payload::Domain { ty, .. }) = &mut nodes[domain].payload else {
                unreachable!()
            };
            *ty = swapped.clone();
            for member in elements {
                nodes[member.0].ty = NodeType::Value(swapped.clone());
                let Some(Payload::Scalar(Scalar::Tuple(values))) = &mut nodes[member.0].payload
                else {
                    unreachable!()
                };
                values.swap(0, 1);
            }
        });
        let record = result
            .cases
            .iter()
            .find(|record| record.seed == NodeRef(seed))
            .unwrap();
        assert_eq!(record.values.len(), 2);
        assert_eq!(
            result.nodes[record.values[0].0].ty,
            NodeType::Value(Type::Fp("2".into()))
        );
        assert_eq!(
            result.nodes[record.values[1].0].ty,
            NodeType::Value(Type::Bool)
        );
        let projection = record.values[0].0;
        completion_mutation(&result, projection, |nodes| {
            nodes[projection].ty = NodeType::Value(Type::Bool);
            nodes[projection].payload = Some(Payload::Scalar(Scalar::Bool(false)));
        });
        let pair = result.answers[0]
            .evidence
            .iter()
            .find(|r| {
                matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::CompletionPair { .. })
                )
            })
            .unwrap()
            .0;
        completion_mutation(&result, pair, |nodes| {
            let Some(Payload::CompletionPair { fields, .. }) = &mut nodes[pair].payload else {
                unreachable!()
            };
            fields.swap(0, 1);
        });
        for scalar in fp_completion_field_scalars(&result, b"s.f") {
            assert!(result.nodes[scalar].support.is_empty());
            assert_eq!(
                result.nodes[scalar].ty,
                NodeType::Value(Type::Fp("2".into()))
            );
        }
    }
    #[test]
    fn fp_completion_prefixes_reject_foreign_call_case_and_request_producers() {
        let result = fp_completion_example(
            "view read(x:Sample):Fp(2)=x.f; view paired(s:Sample,t:Sample):Fp(2)=read(s)-read(t);",
            &[
                "first=evaluate(Calc.paired,s=@v/sample,t=@v/sample)",
                "again=evaluate(Calc.paired,s=@v/sample,t=@v/sample)",
            ],
        );
        assert_eq!(result.status(), "complete");
        let fields = fp_completion_field_scalars(&result, b"x.f");
        assert_eq!(fields.len(), 8);
        for (foreign, target) in [
            (fields[0], fields[1]),
            (fields[0], fields[2]),
            (fields[0], fields[4]),
        ] {
            let (old, own) = (
                result.nodes[foreign].arguments[1],
                result.nodes[target].arguments[1],
            );
            assert_ne!(old, own);
            assert_eq!(
                data_scalar_at(&result, old.0),
                data_scalar_at(&result, own.0)
            );
            completion_mutation(&result, target, |nodes| nodes[target].arguments[1] = old);
        }
        assert_eq!(
            data_scalar_at(&result, fields[0]),
            data_scalar_at(&result, fields[1])
        );
        completion_mutation(&result, fields[1], |nodes| {
            nodes[fields[1]].arguments[0] = result.nodes[fields[0]].arguments[0]
        });
        let Signature::View { body, .. } =
            &result.prepared.inputs().law().declarations["Calc.paired"].signature
        else {
            unreachable!()
        };
        let span = result.prepared.inputs().law().exprs[*body].span;
        let roots:Vec<_>=result.nodes.iter().enumerate().filter_map(|(i,node)| {
            (result.contexts[i].case.is_some() && result.contexts[i].frame.is_none() && result.contexts[i].iteration.is_none() && result.contexts[i].instance.is_none()
                && matches!(&node.payload,Some(Payload::Evaluation {expression,..}) if matches!(&result.nodes[expression.0].payload,Some(Payload::Expression {location:Location::Law {span:actual},..}) if *actual==span))).then_some(i)
        }).collect();
        assert_eq!(roots.len(), 4);
        for target in [roots[1], roots[2]] {
            let value = |index: usize| {
                let Some(Payload::Evaluation {
                    value: Some(value), ..
                }) = &result.nodes[index].payload
                else {
                    unreachable!()
                };
                *value
            };
            let (foreign, own) = (value(roots[0]), value(target));
            assert_ne!(foreign, own);
            assert_eq!(
                data_scalar_at(&result, foreign.0),
                data_scalar_at(&result, own.0)
            );
            completion_mutation(&result, target, |nodes| {
                let Some(Payload::Evaluation { value, parts, .. }) = &mut nodes[target].payload
                else {
                    unreachable!()
                };
                *value = Some(foreign);
                parts[0].value = Some(foreign);
                for argument in &mut nodes[target].arguments {
                    if *argument == own {
                        *argument = foreign;
                    }
                }
            });
        }
    }
    #[test]
    fn fp_completion_law_families_recheck_instance_producers_and_case_coverage() {
        let result = fp_completion_example(
            "law required related(s:Sample,b:Fp(2)):b=s.f;",
            &["family=check(Calc.related,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        assert_eq!(result.answers[0].status, Decision::Refuted);
        let proof = result.answers[0]
            .evidence
            .iter()
            .find(|r| {
                matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::FiniteExhaustion { .. })
                )
            })
            .unwrap()
            .0;
        let Some(Payload::FiniteExhaustion {
            instances, checked, ..
        }) = &result.nodes[proof].payload
        else {
            unreachable!()
        };
        assert_eq!(*checked, 2);
        assert_eq!(instances.len(), 2);
        for &case in instances {
            let context = result.contexts[case.0];
            let record = &result.cases[context.case.unwrap()];
            let assignment = data_scalar_at(&result, record.values[0].0);
            assert!(
                matches!(&result.nodes[case.0].payload,Some(Payload::Evaluation {value:Some(v),parts,..}) if data_scalar_at(&result,v.0)==&Scalar::Bool(false) && parts[0].children.len()==2)
            );
            assert!(result.nodes.iter().enumerate().any(|(i,node)|result.contexts[i].case==context.case && matches!(&node.payload,Some(Payload::Counterexample {bindings,..}) if bindings.iter().any(|b|b.name=="b" && data_scalar_at(&result,b.value.0)!=assignment))));
        }
        for variant in 0..3 {
            completion_mutation(&result, proof, |nodes| {
                let Some(Payload::FiniteExhaustion {
                    checked, instances, ..
                }) = &mut nodes[proof].payload
                else {
                    unreachable!()
                };
                match variant {
                    0 => *checked += 1,
                    1 => {
                        instances[1] = instances[0];
                        nodes[proof].arguments[3] = nodes[proof].arguments[2];
                    }
                    _ => {
                        instances.pop();
                        nodes[proof].arguments.pop();
                    }
                }
            });
        }
        let fields = fp_completion_field_scalars(&result, b"s.f");
        assert_eq!(fields.len(), 4);
        assert_eq!(
            result.contexts[fields[0]].case,
            result.contexts[fields[1]].case
        );
        assert_ne!(
            result.contexts[fields[0]].instance,
            result.contexts[fields[1]].instance
        );
        assert_eq!(
            data_scalar_at(&result, fields[0]),
            data_scalar_at(&result, fields[1])
        );
        completion_mutation(&result, fields[1], |nodes| {
            nodes[fields[1]].arguments[0] = result.nodes[fields[0]].arguments[0]
        });
    }
    #[test]
    fn fp_completion_pairs_recheck_original_field_assignment_and_result() {
        let result = fp_completion_example(
            "view observe(s:Sample):Fp(3)=s.g;",
            &["first=evaluate(Calc.observe,s=@v/sample)"],
        );
        assert_eq!(result.status(), "partial");
        assert!(!result.answers[0].outputs.contains_key("value"));
        let pair = result.answers[0]
            .evidence
            .iter()
            .find(|r| {
                matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::CompletionPair { .. })
                )
            })
            .unwrap()
            .0;
        let Some(Payload::CompletionPair {
            first,
            second,
            first_result,
            second_result,
            ..
        }) = &result.nodes[pair].payload
        else {
            unreachable!()
        };
        for value in first.iter().chain(second) {
            assert_eq!(
                result.nodes[value.0].ty,
                NodeType::Value(Type::Fp("3".into()))
            );
        }
        assert_ne!(
            data_scalar_at(&result, first[0].0),
            data_scalar_at(&result, second[0].0)
        );
        assert_ne!(first_result, second_result);
        let root = result.answers[0].outputs["evaluation"].0;
        let seed = result.nodes[root].arguments[0];
        let third = result
            .cases
            .iter()
            .filter(|case| case.seed == seed)
            .nth(2)
            .unwrap()
            .values[0];
        for variant in 0..3 {
            completion_mutation(&result, pair, |nodes| {
                let Some(Payload::CompletionPair {
                    fields,
                    first,
                    second_result,
                    first_result,
                    ..
                }) = &mut nodes[pair].payload
                else {
                    unreachable!()
                };
                match variant {
                    0 => fields[0].field = Some("FiniteScalar.Sample.f".into()),
                    1 => {
                        first[0] = third;
                        nodes[pair].arguments[4] = third;
                    }
                    _ => {
                        *second_result = *first_result;
                        nodes[pair].arguments[3] = nodes[pair].arguments[2];
                    }
                }
            });
        }
    }
    #[test]
    fn fp_completion_scopes_support_order_and_fresh_sessions_remain_exact() {
        let result = fp_completion_example(
            "view stable(s:Sample):Fp(2)=s.f-s.f;",
            &["first=evaluate(Calc.stable,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        let root = result.answers[0].outputs["evaluation"].0;
        let scalar = result.answers[0].outputs["value"].0;
        let domain = result.nodes[root].arguments[1].0;
        let seed = result.nodes[domain].arguments[0].0;
        let proof = result.answers[0].evidence[0].0;
        let fact = result.nodes[scalar].support.first().unwrap().clone();
        for target in [seed, scalar, proof] {
            completion_mutation(&result, target, |nodes| {
                if nodes[target].support.is_empty() {
                    nodes[target].support.push(fact.clone());
                } else {
                    nodes[target].support.clear();
                }
            });
        }
        for target in [domain, scalar, root] {
            completion_mutation(&result, target, |nodes| {
                assert!(nodes[target].scope.snapshots.remove("v"));
            });
        }
        completion_mutation(&result, scalar, |nodes| {
            nodes[scalar].payload = Some(Payload::Scalar(Scalar::Fp {
                modulus: "2".into(),
                value: 1.into(),
            }))
        });
        let mut reordered = result.nodes.clone();
        let Some(Payload::Domain { elements, .. }) = &mut reordered[domain].payload else {
            unreachable!()
        };
        elements.reverse();
        reordered[domain].arguments[1..].reverse();
        let Some(Payload::FiniteExhaustion { instances, .. }) = &mut reordered[proof].payload
        else {
            unreachable!()
        };
        instances.reverse();
        reordered[proof].arguments[2..].reverse();
        let Some(Payload::Evaluation { parts, .. }) = &mut reordered[root].payload else {
            unreachable!()
        };
        parts[0].children.reverse();
        reordered[root].arguments[2..].reverse();
        reordered[scalar].arguments[2..].reverse();
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        let mut graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let mut control = named_call_quiet();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        environment
            .recheck_node(&graph, &graph.nodes[scalar], scalar)
            .unwrap();
        let original = graph.nodes[seed].scope.clone();
        assert!(graph.nodes[seed].scope.readings.insert("Foreign".into()));
        assert!(matches!(
            environment.recheck_node(&graph, &graph.nodes[scalar], scalar),
            Err(ValidationFailure::Internal(_))
        ));
        graph.nodes[seed].scope = original;
        environment
            .recheck_node(&graph, &graph.nodes[scalar], scalar)
            .unwrap();
    }
    #[test]
    fn fp_completion_enumeration_stop_keeps_original_prefixes() {
        fp_completion_phase_stop("completion_enum", 1, 0, None);
    }
    #[test]
    fn fp_completion_case_stop_keeps_completed_case_and_original_reasons() {
        fp_completion_phase_stop("completion_case", 1, 1, None);
    }
    #[test]
    fn fp_completion_coverage_stop_keeps_cases_without_unfinished_evidence() {
        fp_completion_phase_stop("completion_coverage", 0, 2, None);
    }
    #[test]
    fn fp_completion_enumeration_stop_keeps_verified_original_fp_value() {
        fp_completion_phase_stop("completion_enum", 1, 1, Some(false));
    }
    #[test]
    fn fp_completion_enumeration_stop_keeps_verified_original_law_counterexample() {
        fp_completion_phase_stop("completion_enum", 1, 2, Some(true));
    }
    fn fp_completion_phase_stop(phase: &'static str, at: usize, kind: usize, known: Option<bool>) {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{
            cell::{Cell, RefCell},
            rc::Rc,
        };
        let current = match known {
            Some(true) => "law required current(s:Sample):false and s.f=0;",
            Some(false) => "view current(s:Sample):Fp(2)=if s.f=0 then 1 else 1;",
            None => "view current(s:Sample):Fp(2)=s.f-s.f;",
        };
        let body = format!(
            "view seed():Unit=unit; law required prior(s:Sample):false; view hole(s:Sample):Q=s.q; {current}"
        );
        let inputs = fp_completion_fixture(&body, true);
        let ask = if known == Some(true) {
            "current=check(Calc.current,s=@v/sample)"
        } else {
            "current=evaluate(Calc.current,s=@v/sample)"
        };
        let asks = [
            "seed=evaluate(Calc.seed)",
            "prior=check(Calc.prior,s=@v/sample)",
            "hole=evaluate(Calc.hole,s=@v/sample)",
            ask,
            "later=evaluate(Calc.seed)",
        ];
        let mut quiet = named_call_quiet();
        let prepared = prepare_observed(inputs.clone(), &asks, &mut quiet).unwrap();
        let declaration = &prepared.inputs().law().declarations["Calc.current"];
        let target = declaration.span;
        let body_id = match &declaration.signature {
            Signature::View { body, .. } | Signature::Law { body, .. } => *body,
            _ => unreachable!(),
        };
        let body_span = prepared.inputs().law().exprs[body_id].span;
        let progress = Rc::new(RefCell::new(Vec::new()));
        let observed = progress.clone();
        let normal = evaluate_observed_with_validator(
            prepared,
            &mut quiet,
            |environment, graph, request, answer| {
                environment.validate_answer(graph, request, answer)?;
                if request.id == "hole" {
                    let observed = observed.clone();
                    data::observe_iterations(move |span, context, operation, index| {
                        if span == target
                            && context.request == 3
                            && context.case.is_none()
                            && operation == phase
                        {
                            observed.borrow_mut().push(index);
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
        assert!(normal.answers[1].evidence.iter().any(|r| matches!(
            &normal.nodes[r.0].payload,
            Some(Payload::Counterexample { .. })
        )));
        assert_eq!(
            normal.answers[3].status,
            if known == Some(true) {
                Decision::Refuted
            } else {
                Decision::Established
            }
        );
        assert_eq!(
            &*progress.borrow(),
            if phase == "completion_coverage" {
                &[0][..]
            } else {
                &[0, 1][..]
            }
        );
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        let original = if let Some(check) = known {
            let roots:Vec<_>=normal.nodes.iter().enumerate().filter_map(|(index,node)| {
                let context=normal.contexts[index];
                (context.request==3 && context.case.is_none() && context.frame.is_none() && context.iteration.is_none() && context.instance.is_none()
                    && matches!(&node.payload,Some(Payload::Evaluation {expression,..}) if matches!(&normal.nodes[expression.0].payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==body_span))).then_some(NodeRef(index))
            }).collect();
            assert_eq!(roots.len(), 1);
            let root = roots[0];
            let Some(Payload::Evaluation {
                value: Some(value), ..
            }) = &normal.nodes[root.0].payload
            else {
                panic!("verified known observed root")
            };
            let value = *value;
            assert_eq!(
                data_scalar_at(&normal, value.0),
                &if check {
                    Scalar::Bool(false)
                } else {
                    Scalar::Fp {
                        modulus: "2".into(),
                        value: 1.into(),
                    }
                }
            );
            rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..=value.0]).unwrap();
            let proposition = if check {
                let props: Vec<_> = normal
                    .nodes
                    .iter()
                    .enumerate()
                    .filter_map(|(i, node)| {
                        (normal.contexts[i].request == 3
                            && normal.contexts[i].case.is_none()
                            && matches!(&node.payload, Some(Payload::Proposition { .. }))
                            && node.arguments.get(1) == Some(&root))
                        .then_some(NodeRef(i))
                    })
                    .collect();
                assert_eq!(props.len(), 1);
                let reference = props[0];
                assert!(normal.nodes[reference.0].evidence.iter().any(|r| matches!(
                    &normal.nodes[r.0].payload,
                    Some(Payload::Counterexample { .. })
                )));
                rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..=reference.0])
                    .unwrap();
                Some(reference)
            } else {
                None
            };
            Some((root, value, proposition))
        } else {
            None
        };
        let (limits, usage, expected) = match kind {
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
        let prepared = prepare_observed(inputs, &asks, &mut control).unwrap();
        let seen = Rc::new(RefCell::new(Vec::new()));
        let observed = seen.clone();
        let stopped = evaluate_observed_with_validator(
            prepared,
            &mut control,
            |environment, graph, request, answer| {
                environment.validate_answer(graph, request, answer)?;
                if request.id == "hole" {
                    let (observed, armed) = (observed.clone(), armed.clone());
                    data::observe_iterations(move |span, context, operation, index| {
                        if span == target
                            && context.request == 3
                            && context.case.is_none()
                            && operation == phase
                        {
                            observed.borrow_mut().push(index);
                            if index == at {
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
        assert_eq!(seen.borrow().last(), Some(&at));
        assert_eq!(control.stop_reason(), Some(expected.clone()));
        assert_eq!(Some(probes.get()), frozen.get());
        assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
        let Json::Obj(ref normal_wire) = normal.wire() else {
            unreachable!()
        };
        let Json::Arr(normal_answers) = &normal_wire["answers"] else {
            unreachable!()
        };
        let Json::Obj(ref stopped_wire) = stopped.wire() else {
            unreachable!()
        };
        let Json::Arr(stopped_answers) = &stopped_wire["answers"] else {
            unreachable!()
        };
        assert_eq!(&stopped_answers[..3], &normal_answers[..3]);
        if let Some((root, value, proposition)) = original {
            assert_eq!(stopped.answers[3].status, normal.answers[3].status);
            assert_eq!(stopped.answers[3].outputs.get("evaluation"), Some(&root));
            assert_eq!(stopped.answers[3].claim, proposition);
            if let Some(proposition) = proposition {
                assert_eq!(
                    stopped.answers[3].evidence,
                    normal.nodes[proposition.0].evidence
                );
                assert!(stopped.answers[3].evidence.iter().any(|r| matches!(
                    &stopped.nodes[r.0].payload,
                    Some(Payload::Counterexample { .. })
                )));
            } else {
                assert_eq!(stopped.answers[3].outputs.get("value"), Some(&value));
            }
        } else {
            assert_eq!(stopped.answers[3].status, Decision::Undetermined);
            assert!(stopped.answers[3].outputs.is_empty());
            assert!(stopped.answers[3].evidence.is_empty());
        }
        assert!(
            stopped.answers[3]
                .reasons
                .iter()
                .flat_map(|reason| &reason.missing)
                .any(|fact| fact.field.as_deref() == Some("FiniteScalar.Sample.f"))
        );
        assert_eq!(stopped.answers[4].status, Decision::Undetermined);
        assert!(stopped.answers[4].outputs.is_empty());
        for answer in &stopped.answers[3..] {
            let reason = answer
                .reasons
                .iter()
                .find(|r| matches!(&r.kind,ReasonKind::Stop(actual) if actual==&expected))
                .unwrap();
            let Json::Obj(ref wire) = reason.wire() else {
                unreachable!()
            };
            let Json::Obj(ref expected_wire) = expected.wire() else {
                unreachable!()
            };
            assert_eq!(wire.get("details"), expected_wire.get("details"));
        }
        let completed=stopped.nodes.iter().enumerate().filter(|(i,node)|stopped.contexts[*i].request==3 && stopped.contexts[*i].case.is_some() && stopped.contexts[*i].frame.is_none() && stopped.contexts[*i].iteration.is_none() && stopped.contexts[*i].instance.is_none()
            && matches!(&node.payload,Some(Payload::Evaluation {expression,..}) if matches!(&stopped.nodes[expression.0].payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==body_span))).count();
        assert_eq!(
            completed,
            if phase == "completion_enum" {
                0
            } else if phase == "completion_case" {
                1
            } else {
                2
            }
        );
        assert!(
            !stopped
                .nodes
                .iter()
                .enumerate()
                .any(|(i, node)| stopped.contexts[i].request == 3
                    && matches!(
                        &node.payload,
                        Some(Payload::FiniteExhaustion { .. } | Payload::CompletionPair { .. })
                    ))
        );
        rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
        let before = probes.get();
        assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
        assert_eq!(probes.get(), before);
    }
    #[test]
    fn fp_completion_recheck_entry_stops_keep_graph_and_original_reason() {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{cell::Cell, rc::Rc};
        let result = fp_completion_example(
            "view stable(s:Sample):Fp(2)=s.f-s.f;",
            &["first=evaluate(Calc.stable,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        let scalar = result.answers[0].outputs["value"].0;
        let graph =
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
        let snapshot = || {
            format!(
                "{:?}",
                (
                    &graph.nodes,
                    &graph.contexts,
                    &graph.frames,
                    &graph.iterations,
                    &graph.instances,
                    &graph.cases
                )
            )
        };
        let before = snapshot();
        for kind in 0..3 {
            let (limits, usage, expected) = match kind {
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
            let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
            environment
                .recheck_node(&graph, &graph.nodes[scalar], scalar)
                .unwrap();
            let prior = probes.get();
            armed.set(true);
            let failure = environment
                .recheck_node(&graph, &graph.nodes[scalar], scalar)
                .unwrap_err();
            let ValidationFailure::Stop(actual) = failure else {
                panic!("Fp再照合のStopを保持する")
            };
            assert_eq!(actual, expected);
            assert_eq!(actual.wire(), expected.wire());
            assert_eq!(probes.get(), prior + 1);
            assert_eq!(Some(probes.get()), frozen.get());
            assert_eq!(snapshot(), before);
            assert!(
                matches!(environment.recheck_node(&graph,&graph.nodes[scalar],scalar),Err(ValidationFailure::Stop(actual)) if actual==expected)
            );
            assert_eq!(Some(probes.get()), frozen.get());
            assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
            assert_eq!(Some(probes.get()), frozen.get());
        }
        rebuild_for_origin_and_support_recheck(&result, &graph.nodes).unwrap();
    }
    fn completion_private_example(body: &str, asks: &[&str]) -> ObservedEvaluation {
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(&["p"], body),
            asks,
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_ne!(result.status(), "error", "{:?}", result.issues);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        result
    }
    fn completion_mutation(
        result: &ObservedEvaluation,
        target: usize,
        change: impl Fn(&mut [Node]),
    ) {
        rebuild_for_origin_and_support_recheck(result, &result.nodes[..=target]).unwrap();
        let mut prefix = result.nodes[..=target].to_vec();
        change(&mut prefix);
        assert_ne!(
            format!("{prefix:?}"),
            format!("{:?}", &result.nodes[..=target]),
            "mutation must change a claim"
        );
        rejects_named_prefix(result, &prefix);
        let mut full = result.nodes.clone();
        change(&mut full);
        rejects_named_prefix(result, &full);
    }
    #[test]
    fn bool_completion_domains_recheck_slots_assignments_and_sources() {
        let result = completion_private_example(
            "view stable(s:Sample):Bool=s.p or not s.p;",
            &["first=evaluate(Calc.stable,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        assert_eq!(result.answers[0].status, Decision::Established);
        let domain = result.nodes[result.answers[0].outputs["evaluation"].0].arguments[1].0;
        let seed = result.nodes[domain].arguments[0].0;
        for variant in 0..4 {
            completion_mutation(&result, domain, |nodes| match variant {
                0 => {
                    let Some(Payload::Domain { ty, .. }) = &mut nodes[domain].payload else {
                        unreachable!()
                    };
                    *ty = Type::Unit;
                }
                1 => {
                    let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
                        unreachable!()
                    };
                    elements.pop();
                    nodes[domain].arguments.pop();
                }
                2 => {
                    let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
                        unreachable!()
                    };
                    elements[1] = elements[0];
                    nodes[domain].arguments[2] = nodes[domain].arguments[1];
                }
                _ => {
                    let Some(Payload::CompletionSeed { fields, .. }) = &mut nodes[seed].payload
                    else {
                        unreachable!()
                    };
                    fields[0].field = Some("Numeric.Sample.q".into());
                }
            });
        }
        let law = result.prepared.inputs().sources().law().bytes();
        let fields:Vec<_>=result.nodes.iter().enumerate().filter_map(|(i,node)| {
            (result.contexts[i].case.is_some() && node.arguments.len()==3
                && matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span}} if &law[span.0..span.1]==b"s.p")
                && matches!(&node.payload,Some(Payload::Scalar(Scalar::Bool(_)))))
                .then_some(i)
        }).collect();
        assert_eq!(fields.len(), 4);
        let projection = result.nodes[fields[0]].arguments[2].0;
        completion_mutation(&result, projection, |nodes| {
            let Some(Payload::Scalar(value)) = &mut nodes[projection].payload else {
                unreachable!()
            };
            let Scalar::Bool(value) = value else {
                unreachable!()
            };
            *value = !*value;
        });
        let source = result.nodes[fields[0]].arguments[0].0;
        completion_mutation(&result, source, |nodes| {
            let Some(Payload::Expression { bindings, .. }) = &mut nodes[source].payload else {
                unreachable!()
            };
            bindings[0].name = "foreign".into();
        });
    }
    #[test]
    fn bool_completion_field_prefixes_reject_other_call_case_and_request_owners() {
        let result = completion_private_example(
            "view read(x:Sample):Bool=x.p; view correlated(s:Sample,t:Sample):Bool=read(s) or not read(t);",
            &[
                "first=evaluate(Calc.correlated,s=@v/sample,t=@v/sample)",
                "again=evaluate(Calc.correlated,s=@v/sample,t=@v/sample)",
            ],
        );
        assert_eq!(result.status(), "complete");
        assert_eq!(result.answers[0].status, Decision::Established);
        let law = result.prepared.inputs().sources().law().bytes();
        let fields:Vec<_>=result.nodes.iter().enumerate().filter_map(|(i,node)| {
            (result.contexts[i].case.is_some() && node.arguments.len()==3
                && matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span}} if &law[span.0..span.1]==b"x.p")
                && matches!(&node.payload,Some(Payload::Scalar(Scalar::Bool(_)))))
                .then_some(i)
        }).collect();
        assert_eq!(fields.len(), 8);
        // 同値を与えたs/tは同じcaseでも元selectorのproducerが異なる。
        for (foreign, target) in [
            (fields[0], fields[1]),
            (fields[0], fields[2]),
            (fields[0], fields[4]),
        ] {
            let (old, own) = (
                result.nodes[foreign].arguments[1],
                result.nodes[target].arguments[1],
            );
            assert_ne!(old, own);
            assert_eq!(
                data_scalar_at(&result, old.0),
                data_scalar_at(&result, own.0)
            );
            completion_mutation(&result, target, |nodes| nodes[target].arguments[1] = old);
        }
    }
    #[test]
    fn bool_completion_whole_law_families_recheck_case_coverage() {
        let result = completion_private_example(
            "law required related(s:Sample,b:Bool):b=s.p;",
            &["related=check(Calc.related,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        assert_eq!(result.answers[0].status, Decision::Refuted);
        let proof = result.answers[0].evidence[0].0;
        let Some(Payload::FiniteExhaustion {
            instances, checked, ..
        }) = &result.nodes[proof].payload
        else {
            panic!("all-false case coverage")
        };
        assert_eq!(*checked, 2);
        assert_eq!(instances.len(), 2);
        let aggregate = &result.nodes[result.answers[0].outputs["evaluation"].0];
        for (index, reason) in aggregate.reasons.iter().enumerate() {
            assert!(
                aggregate.reasons[..index]
                    .iter()
                    .all(|old| old.wire() != reason.wire())
            );
        }
        for case in instances {
            assert_eq!(result.nodes[case.0].ty, NodeType::Evaluation(Type::Bool));
            assert!(
                matches!(&result.nodes[case.0].payload,Some(Payload::Evaluation {value:Some(v),..}) if data_scalar_at(&result,v.0)==&Scalar::Bool(false))
            );
            let context = result.contexts[case.0];
            assert!(
                result
                    .nodes
                    .iter()
                    .enumerate()
                    .any(|(i, node)| result.contexts[i].case == context.case
                        && matches!(&node.payload, Some(Payload::Counterexample { .. })))
            );
        }
        for case in instances {
            for reason in &result.nodes[case.0].reasons {
                assert!(
                    aggregate
                        .reasons
                        .iter()
                        .any(|retained| retained.wire() == reason.wire())
                );
            }
        }
        for variant in 0..3 {
            completion_mutation(&result, proof, |nodes| {
                let Some(Payload::FiniteExhaustion {
                    checked, instances, ..
                }) = &mut nodes[proof].payload
                else {
                    unreachable!()
                };
                match variant {
                    0 => *checked += 1,
                    1 => {
                        instances[1] = instances[0];
                        nodes[proof].arguments[3] = nodes[proof].arguments[2];
                    }
                    _ => {
                        instances.pop();
                        nodes[proof].arguments.pop();
                    }
                }
            });
        }
    }
    #[test]
    fn bool_completion_pairs_and_inapplicable_cases_recheck_evidence() {
        let result = completion_private_example(
            "law required gated(s:Sample) when s.p:false; view stable(s:Sample):Q=if s.p then s.q else s.q;",
            &[
                "seed=evaluate(Calc.stable,s=@v/sample)",
                "gated=check(Calc.gated,s=@v/sample)",
                "stable=evaluate(Calc.stable,s=@v/sample)",
            ],
        );
        assert_eq!(result.status(), "partial");
        assert_eq!(result.answers[0].status, Decision::Established);
        assert_eq!(result.answers[1].status, Decision::Undetermined);
        assert_eq!(result.answers[2].status, Decision::Established);
        let proof = result.answers[0].evidence[0].0;
        let pair = result.answers[1]
            .evidence
            .iter()
            .find(|r| {
                matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::CompletionPair { .. })
                )
            })
            .unwrap()
            .0;
        for variant in 0..3 {
            completion_mutation(&result, pair, |nodes| {
                let Some(Payload::CompletionPair {
                    fields,
                    first,
                    second,
                    first_result,
                    second_result,
                }) = &mut nodes[pair].payload
                else {
                    unreachable!()
                };
                match variant {
                    0 => fields[0].snapshot = "foreign".into(),
                    1 => {
                        *second = first.clone();
                        let n = nodes[pair].arguments.len();
                        nodes[pair].arguments[n - 1] = nodes[pair].arguments[n - 2];
                    }
                    _ => {
                        *second_result = *first_result;
                        nodes[pair].arguments[3] = nodes[pair].arguments[2];
                    }
                }
            });
        }
        let stable = result.answers[2].outputs["value"].0;
        completion_mutation(&result, stable, |nodes| {
            nodes[stable].evidence = vec![NodeRef(pair)]
        });
        let skipped = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(i, n)| {
                (result.contexts[i].request == 1
                    && result.contexts[i].case.is_some()
                    && matches!(
                        &n.payload,
                        Some(Payload::Evaluation {
                            applicability: "not_applicable",
                            ..
                        })
                    ))
                .then_some(i)
            })
            .unwrap();
        let Some(Payload::Evaluation { parts, .. }) = &result.nodes[skipped].payload else {
            unreachable!()
        };
        assert_eq!(parts.len(), 2);
        assert!(parts[1].value.is_none() && parts[1].children.is_empty());
        completion_mutation(&result, skipped, |nodes| {
            nodes[skipped].evidence = vec![NodeRef(proof)]
        });
    }
    #[test]
    fn bool_completion_scopes_support_and_source_origins_remain_exact() {
        let result = completion_private_example(
            "view stable(s:Sample):Q=if s.p then s.q else s.q;",
            &["first=evaluate(Calc.stable,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        let evaluation = result.answers[0].outputs["evaluation"].0;
        let scalar = result.answers[0].outputs["value"].0;
        let domain = result.nodes[evaluation].arguments[1].0;
        let seed = result.nodes[domain].arguments[0].0;
        let fact = result.nodes[scalar]
            .support
            .iter()
            .find(|f| f.atom.is_some())
            .unwrap()
            .clone();
        for target in [seed, domain, scalar, evaluation] {
            completion_mutation(&result, target, |nodes| {
                if nodes[target].support.is_empty() {
                    nodes[target].support.push(fact.clone());
                } else {
                    nodes[target].support.clear();
                }
            });
            completion_mutation(&result, target, |nodes| {
                assert!(nodes[target].scope.snapshots.remove("v"));
            });
        }
        completion_mutation(&result, seed, |nodes| {
            let Some(Payload::CompletionSeed { location, .. }) = &mut nodes[seed].payload else {
                unreachable!()
            };
            *location = Location::Law { span: (0, 1) };
            nodes[seed].rule = Rule::Input {
                kind: "law",
                location: Location::Law { span: (0, 1) },
            };
        });
    }
    #[test]
    fn bool_completion_foreign_requests_set_order_and_fresh_sessions_remain_exact() {
        let result = completion_private_example(
            "view stable(s:Sample):Set<Bool> = if s.p then set<Bool>{false,true} else set<Bool>{true,false};",
            &[
                "first=evaluate(Calc.stable,s=@v/sample)",
                "again=evaluate(Calc.stable,s=@v/sample)",
            ],
        );
        assert_eq!(result.status(), "complete");
        let evaluation = result.answers[1].outputs["evaluation"].0;
        let scalar = result.answers[1].outputs["value"].0;
        let domain = result.nodes[evaluation].arguments[1].0;
        let seed = result.nodes[domain].arguments[0].0;
        let Some(Payload::Evaluation { parts, .. }) = &result.nodes[evaluation].payload else {
            unreachable!()
        };
        assert!(
            result
                .answers
                .iter()
                .all(|answer| answer.status == Decision::Established)
        );
        assert!(
            result
                .answers
                .iter()
                .all(|answer| answer.evidence.iter().any(|r| matches!(
                    &result.nodes[r.0].payload,
                    Some(Payload::FiniteExhaustion { checked: 2, .. })
                )))
        );
        assert!(
            !result
                .nodes
                .iter()
                .any(|node| matches!(&node.payload, Some(Payload::CompletionPair { .. })))
        );
        let values: Vec<_> = parts[0]
            .children
            .iter()
            .map(|r| {
                let Some(Payload::Evaluation {
                    value: Some(value), ..
                }) = &result.nodes[r.0].payload
                else {
                    panic!("known case Set")
                };
                data_scalar_at(&result, value.0)
            })
            .collect();
        assert_eq!(values.len(), 2);
        let (Scalar::Set { items: first, .. }, Scalar::Set { items: second, .. }) =
            (values[0], values[1])
        else {
            panic!("typed case Set values")
        };
        assert_ne!(first, second, "the case displays actually differ");
        assert!(data::equal(values[0], values[1], &named_call_quiet()).unwrap());
        let row = parts[0].children[0];
        let previous = result.nodes[result.answers[0].outputs["evaluation"].0].arguments[2];
        assert_ne!(row, previous);
        completion_mutation(&result, evaluation, |nodes| {
            let Some(Payload::Evaluation { parts, .. }) = &mut nodes[evaluation].payload else {
                unreachable!()
            };
            parts[0].children[0] = previous;
            nodes[evaluation].arguments[2] = previous;
        });
        // Domainと全coverageの表示順を一貫して変える。caseの数学的identityはmemberである。
        let proof = result.answers[1].evidence[0].0;
        let mut reordered = result.nodes.clone();
        let Some(Payload::Domain { elements, .. }) = &mut reordered[domain].payload else {
            unreachable!()
        };
        elements.reverse();
        reordered[domain].arguments[1..].reverse();
        let Some(Payload::FiniteExhaustion { instances, .. }) = &mut reordered[proof].payload
        else {
            unreachable!()
        };
        instances.reverse();
        reordered[proof].arguments[2..].reverse();
        let Some(Payload::Evaluation { parts, .. }) = &mut reordered[evaluation].payload else {
            unreachable!()
        };
        parts[0].children.reverse();
        reordered[evaluation].arguments[2..].reverse();
        reordered[scalar].arguments[2..].reverse();
        rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
        // 同じEnvironmentの次session・同じGraphを改変した検査へ成功を持ち越さない。
        let mut graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let mut control = named_call_quiet();
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        environment
            .recheck_node(&graph, &graph.nodes[scalar], scalar)
            .unwrap();
        let original = graph.nodes[seed].scope.clone();
        assert!(graph.nodes[seed].scope.readings.insert("Foreign".into()));
        assert!(matches!(
            environment.recheck_node(&graph, &graph.nodes[scalar], scalar),
            Err(ValidationFailure::Internal(_))
        ));
        graph.nodes[seed].scope = original;
        environment
            .recheck_node(&graph, &graph.nodes[scalar], scalar)
            .unwrap();
    }
    #[test]
    fn bool_completion_actual_enumeration_stop_keeps_prefixes() {
        bool_completion_actual_phase_stop("completion_enum", 1, 0);
    }
    #[test]
    fn bool_completion_actual_case_stop_keeps_prefixes() {
        bool_completion_actual_phase_stop("completion_case", 1, 1);
    }
    #[test]
    fn bool_completion_actual_coverage_stop_keeps_prefixes() {
        bool_completion_actual_phase_stop("completion_coverage", 0, 2);
    }
    #[test]
    fn bool_completion_recheck_entry_stops_preserve_graph_and_reason() {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{cell::Cell, rc::Rc};
        let result = completion_private_example(
            "view stable(s:Sample):Bool=s.p or not s.p;",
            &["first=evaluate(Calc.stable,s=@v/sample)"],
        );
        assert_eq!(result.status(), "complete");
        let scalar = result.answers[0].outputs["value"].0;
        let graph =
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
        let snapshot = || {
            format!(
                "{:?}",
                (
                    &graph.nodes,
                    &graph.contexts,
                    &graph.frames,
                    &graph.iterations,
                    &graph.instances,
                    &graph.cases
                )
            )
        };
        let before = snapshot();
        // 深い全停止点ではなく、補完Scalar再照合の入口の一つの既存tickを検査する。
        for kind in 0..3 {
            let (limits, usage, expected) = match kind {
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
            let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
            environment
                .recheck_node(&graph, &graph.nodes[scalar], scalar)
                .unwrap();
            let normal_probes = probes.get();
            armed.set(true);
            let failure = environment
                .recheck_node(&graph, &graph.nodes[scalar], scalar)
                .unwrap_err();
            let ValidationFailure::Stop(actual) = failure else {
                panic!("補完再照合のStopをInternalへ変えない")
            };
            assert_eq!(actual, expected);
            assert_eq!(actual.wire(), expected.wire());
            assert_eq!(probes.get(), normal_probes + 1);
            assert_eq!(Some(probes.get()), frozen.get());
            assert_eq!(snapshot(), before);
            assert!(
                matches!(environment.recheck_node(&graph,&graph.nodes[scalar],scalar),Err(ValidationFailure::Stop(actual)) if actual==expected)
            );
            assert_eq!(Some(probes.get()), frozen.get());
            assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
            assert_eq!(Some(probes.get()), frozen.get());
        }
        rebuild_for_origin_and_support_recheck(&result, &graph.nodes).unwrap();
    }
    #[test]
    fn bool_completion_enumeration_stop_retains_verified_original_view_value() {
        bool_completion_known_original_stop(false);
    }
    #[test]
    fn bool_completion_enumeration_stop_retains_verified_original_law_counterexample() {
        bool_completion_known_original_stop(true);
    }
    fn bool_completion_known_original_stop(check: bool) {
        use super::super::control::{Limits, Usage};
        use crate::result::Signal;
        use std::{
            cell::{Cell, RefCell},
            rc::Rc,
        };
        let body = if check {
            "view seed():Unit=unit; law required current(s:Sample):false and s.p;"
        } else {
            "view seed():Unit=unit; view current(s:Sample):Bool=false and s.p;"
        };
        let inputs = numeric_recheck_fixture(&["p"], body);
        let current = if check {
            "current=check(Calc.current,s=@v/sample)"
        } else {
            "current=evaluate(Calc.current,s=@v/sample)"
        };
        let asks = [
            "seed=evaluate(Calc.seed)",
            current,
            "later=evaluate(Calc.seed)",
        ];
        let mut quiet = named_call_quiet();
        let prepared = prepare_observed(inputs.clone(), &asks, &mut quiet).unwrap();
        let declaration = &prepared.inputs().law().declarations["Calc.current"];
        let target = declaration.span;
        let body_id = match &declaration.signature {
            Signature::View { body, .. } | Signature::Law { body, .. } => *body,
            _ => unreachable!(),
        };
        let body_span = prepared.inputs().law().exprs[body_id].span;
        let normal = evaluate_observed(prepared, &mut quiet).unwrap();
        assert_eq!(normal.status(), "complete", "{:?}", normal.issues);
        assert_eq!(
            normal.answers[1].status,
            if check {
                Decision::Refuted
            } else {
                Decision::Established
            }
        );
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
        let raw:Vec<_>=normal.nodes.iter().enumerate().filter_map(|(index,node)| {
            let context=normal.contexts[index];
            if context.request!=1 || context.case.is_some() || context.frame.is_some() || context.iteration.is_some() || context.instance.is_some() {return None;}
            (matches!(&node.payload,Some(Payload::Evaluation {expression,..}) if matches!(&normal.nodes[expression.0].payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==body_span))).then_some(index)
        }).collect();
        assert_eq!(raw.len(), 1);
        let raw = NodeRef(raw[0]);
        let Some(Payload::Evaluation {
            value: Some(value), ..
        }) = &normal.nodes[raw.0].payload
        else {
            panic!("known observed false")
        };
        let value = *value;
        assert_eq!(data_scalar_at(&normal, value.0), &Scalar::Bool(false));
        rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..=value.0]).unwrap();
        let original_prop = if check {
            let refs: Vec<_> = normal
                .nodes
                .iter()
                .enumerate()
                .filter_map(|(index, node)| {
                    (normal.contexts[index].request == 1
                        && normal.contexts[index].case.is_none()
                        && matches!(&node.payload, Some(Payload::Proposition { .. }))
                        && node.arguments.get(1) == Some(&raw))
                    .then_some(NodeRef(index))
                })
                .collect();
            assert_eq!(refs.len(), 1);
            let proposition = refs[0];
            assert_eq!(
                normal.nodes[proposition.0]
                    .judgment
                    .as_ref()
                    .unwrap()
                    .status,
                Decision::Refuted
            );
            assert!(
                normal.nodes[proposition.0]
                    .evidence
                    .iter()
                    .any(|r| matches!(
                        &normal.nodes[r.0].payload,
                        Some(Payload::Counterexample { .. })
                    ))
            );
            rebuild_for_origin_and_support_recheck(&normal, &normal.nodes[..=proposition.0])
                .unwrap();
            Some(proposition)
        } else {
            None
        };
        let armed = Rc::new(Cell::new(false));
        let probes = Rc::new(Cell::new(0));
        let frozen = Rc::new(Cell::new(None));
        let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
        let mut control = Control::new(Limits::default(), move |checkpoint| {
            count.set(count.get() + 1);
            if arm.replace(false) {
                assert_eq!(checkpoint, Checkpoint::FiniteIteration);
                assert!(freeze.replace(Some(count.get())).is_none());
                Usage {
                    signal: Some(Signal::Term),
                    ..Usage::default()
                }
            } else {
                Usage::default()
            }
        });
        let prepared = prepare_observed(inputs, &asks, &mut control).unwrap();
        let seen = Rc::new(RefCell::new(Vec::new()));
        let progress = seen.clone();
        let stopped = evaluate_observed_with_validator(
            prepared,
            &mut control,
            |environment, graph, request, answer| {
                environment.validate_answer(graph, request, answer)?;
                if request.id == "seed" {
                    let (progress, armed) = (progress.clone(), armed.clone());
                    data::observe_iterations(move |span, context, phase, index| {
                        if span == target
                            && context.request == 1
                            && context.case.is_none()
                            && phase == "completion_enum"
                        {
                            progress.borrow_mut().push(index);
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
        let expected = StopReason::Cancelled(Signal::Term);
        assert_eq!(control.stop_reason(), Some(expected.clone()));
        assert_eq!(Some(probes.get()), frozen.get());
        assert_eq!(stopped.status(), "interrupted");
        let Json::Obj(ref normal_wire) = normal.wire() else {
            unreachable!()
        };
        let Json::Arr(normal_answers) = &normal_wire["answers"] else {
            unreachable!()
        };
        let Json::Obj(ref stopped_wire) = stopped.wire() else {
            unreachable!()
        };
        let Json::Arr(stopped_answers) = &stopped_wire["answers"] else {
            unreachable!()
        };
        assert_eq!(stopped_answers[0], normal_answers[0]);
        assert_eq!(
            stopped.answers[1].status,
            if check {
                Decision::Refuted
            } else {
                Decision::Established
            }
        );
        assert_eq!(stopped.answers[1].outputs.get("evaluation"), Some(&raw));
        assert_eq!(stopped.answers[1].claim, original_prop);
        if check {
            let proposition = original_prop.unwrap();
            assert_eq!(
                stopped.answers[1].evidence,
                normal.nodes[proposition.0].evidence
            );
            assert!(stopped.answers[1].evidence.iter().any(|r| matches!(
                &stopped.nodes[r.0].payload,
                Some(Payload::Counterexample { .. })
            )));
        } else {
            assert_eq!(stopped.answers[1].outputs.get("value"), Some(&value));
        }
        assert!(
            stopped.answers[1]
                .reasons
                .iter()
                .flat_map(|reason| &reason.missing)
                .any(|fact| fact.field.as_deref() == Some("Numeric.Sample.p"))
        );
        for answer in &stopped.answers[1..] {
            let reason = answer
                .reasons
                .iter()
                .find(|r| matches!(&r.kind,ReasonKind::Stop(actual) if actual==&expected))
                .unwrap();
            let Json::Obj(ref wire) = reason.wire() else {
                unreachable!()
            };
            let Json::Obj(ref expected_wire) = expected.wire() else {
                unreachable!()
            };
            assert_eq!(wire.get("details"), expected_wire.get("details"));
        }
        assert!(stopped.answers[2].outputs.is_empty());
        assert_eq!(stopped.answers[2].status, Decision::Undetermined);
        assert!(!stopped.nodes.iter().enumerate().any(|(index, node)| {
            stopped.contexts[index].request == 1
                && matches!(
                    &node.payload,
                    Some(
                        Payload::Domain { .. }
                            | Payload::FiniteExhaustion { .. }
                            | Payload::CompletionPair { .. }
                    )
                )
        }));
        rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
        let before = probes.get();
        assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
        assert_eq!(probes.get(), before);
    }
    fn bool_completion_actual_phase_stop(phase: &'static str, at: usize, kind: usize) {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{
            cell::{Cell, RefCell},
            rc::Rc,
        };
        let body = "view seed():Unit=unit; law required prior(s:Sample):s.f=0; view hole(s:Sample):Q=s.q; view current(s:Sample):Bool=s.p or not s.p;";
        let asks = [
            "seed=evaluate(Calc.seed)",
            "prior=check(Calc.prior,s=@v/sample)",
            "hole=evaluate(Calc.hole,s=@v/sample)",
            "current=evaluate(Calc.current,s=@v/sample)",
            "later=evaluate(Calc.seed)",
        ];
        {
            let inputs = numeric_recheck_fixture(&["p", "q"], body);
            let mut quiet = named_call_quiet();
            let prepared = prepare_observed(inputs.clone(), &asks, &mut quiet).unwrap();
            let target = prepared.inputs().law().declarations["Calc.current"].span;
            let Signature::View {
                body: current_body, ..
            } = &prepared.inputs().law().declarations["Calc.current"].signature
            else {
                unreachable!()
            };
            let body_span = prepared.inputs().law().exprs[*current_body].span;
            let progress = Rc::new(RefCell::new(Vec::new()));
            let observed = progress.clone();
            let normal = evaluate_observed_with_validator(
                prepared,
                &mut quiet,
                |environment, graph, request, answer| {
                    environment.validate_answer(graph, request, answer)?;
                    if request.id == "hole" {
                        let observed = observed.clone();
                        data::observe_iterations(move |span, context, operation, index| {
                            if span == target
                                && context.request == 3
                                && context.case.is_none()
                                && operation == phase
                            {
                                observed.borrow_mut().push(index);
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
                if phase == "completion_coverage" {
                    &[0][..]
                } else {
                    &[0, 1][..]
                }
            );
            rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
            let (limits, usage, expected) = match kind {
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
            let prepared = prepare_observed(inputs, &asks, &mut control).unwrap();
            let seen = Rc::new(RefCell::new(Vec::new()));
            let observed = seen.clone();
            let stopped = evaluate_observed_with_validator(
                prepared,
                &mut control,
                |environment, graph, request, answer| {
                    environment.validate_answer(graph, request, answer)?;
                    if request.id == "hole" {
                        let (observed, armed) = (observed.clone(), armed.clone());
                        data::observe_iterations(move |span, context, operation, index| {
                            if span == target
                                && context.request == 3
                                && context.case.is_none()
                                && operation == phase
                            {
                                observed.borrow_mut().push(index);
                                if index == at {
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
            assert_eq!(seen.borrow().last(), Some(&at));
            assert_eq!(control.stop_reason(), Some(expected.clone()));
            assert_eq!(Some(probes.get()), frozen.get());
            assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
            let Json::Obj(ref normal_wire) = normal.wire() else {
                unreachable!()
            };
            let Json::Arr(normal_answers) = &normal_wire["answers"] else {
                unreachable!()
            };
            let Json::Obj(ref stopped_wire) = stopped.wire() else {
                unreachable!()
            };
            let Json::Arr(stopped_answers) = &stopped_wire["answers"] else {
                unreachable!()
            };
            assert_eq!(&stopped_answers[..3], &normal_answers[..3]);
            for answer in &stopped.answers[3..] {
                assert!(answer.outputs.is_empty());
                assert!(answer.evidence.is_empty());
                let reason = answer
                    .reasons
                    .iter()
                    .find(|r| matches!(&r.kind,ReasonKind::Stop(actual) if actual==&expected))
                    .unwrap();
                let Json::Obj(ref rw) = reason.wire() else {
                    unreachable!()
                };
                let Json::Obj(ref ew) = expected.wire() else {
                    unreachable!()
                };
                assert_eq!(rw.get("details"), ew.get("details"));
            }
            assert!(
                stopped.answers[3]
                    .reasons
                    .iter()
                    .flat_map(|r| &r.missing)
                    .any(|f| f.field.as_deref() == Some("Numeric.Sample.p"))
            );
            let expected_cases = if phase == "completion_enum" {
                0
            } else if phase == "completion_case" {
                1
            } else {
                2
            };
            let completed=stopped.nodes.iter().enumerate().filter(|(i,node)| {
                stopped.contexts[*i].request==3 && stopped.contexts[*i].case.is_some()
                    && matches!(&node.payload,Some(Payload::Evaluation {expression,..})
                        if matches!(&stopped.nodes[expression.0].payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==body_span))
            }).count();
            assert_eq!(completed, expected_cases);
            assert!(
                !stopped
                    .nodes
                    .iter()
                    .enumerate()
                    .any(|(i, n)| stopped.contexts[i].request == 3
                        && matches!(
                            &n.payload,
                            Some(Payload::FiniteExhaustion { .. } | Payload::CompletionPair { .. })
                        ))
            );
            rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
            let before = probes.get();
            assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
            assert_eq!(probes.get(), before);
        }
    }
    fn quantifier_actual_phases_preserve_stops(typed: bool, plain: bool) {
        use super::super::control::{Limits, Resource, Usage};
        use crate::result::Signal;
        use std::{
            cell::{Cell, RefCell},
            rc::Rc,
        };
        let phases = if plain {
            vec![
                ("ref_roster", "full", 0),
                ("type_enum", "construct", 1),
                ("quant_domain", "full", 2),
                ("ref_recheck", "full", 0),
            ]
        } else {
            vec![
                (if typed { "type_enum" } else { "quant_domain" }, "full", 0),
                ("quant_body", "early", 1),
                ("quant_exhaustion", "full", 2),
            ]
        };
        for (operation, view, stop) in phases {
            let sources = if plain {
                plain_ref_fixture(false)
            } else if typed {
                type_quantifier_fixture(&["q"])
            } else {
                in_quantifier_fixture(&["q"])
            };
            let current = format!("current=evaluate(Calc.{view})");
            let asks = [
                "seed=evaluate(Calc.later)",
                if plain {
                    "prior=check(Calc.called)"
                } else {
                    "prior=check(Calc.called,x=@v/sample)"
                },
                if plain {
                    "hole=evaluate(Calc.observe,s=@v/item)"
                } else {
                    "hole=evaluate(Calc.observe,s=@v/sample)"
                },
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
                instance: None,
                case: None,
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
            if plain {
                let progress = progress.borrow();
                match operation {
                    "ref_roster" => assert_eq!(&*progress, &[0, 1, 2]),
                    "type_enum" => assert_eq!(&*progress, &[0, 1, 2, 3]),
                    "quant_domain" => assert_eq!(&*progress, &[0, 1]),
                    "ref_recheck" => {
                        assert!(progress.starts_with(&[0, 1]));
                        assert!(progress.iter().all(|index| *index < 2));
                    }
                    _ => unreachable!(),
                }
            } else {
                assert_eq!(
                    &*progress.borrow(),
                    if operation == "quant_exhaustion" {
                        &[0, 1, 2][..]
                    } else {
                        &[0, 1][..]
                    }
                );
            }
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
            if plain {
                assert!(
                    !stopped
                        .nodes
                        .iter()
                        .enumerate()
                        .any(|(index, node)| stopped.contexts[index].request == 3
                            && node.ty == NodeType::Domain)
                );
            }
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
