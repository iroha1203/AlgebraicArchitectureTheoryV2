//! 明示束縛の参照・原始 field・Z/Bool literal・整数比較を原 AST から評価する。
use super::{
    PreparedObserved,
    control::{Checkpoint, Control, StopReason},
    environment::{Environment, SourceAnalysis, binary, scalar_from},
    input::InputSources,
    prepare_observed,
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
            arguments: self.bindings.iter().map(|b| b.value).collect(),
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
                ExprKind::Int(_) if ty == Type::Z => {}
                ExprKind::Bool(_) => {}
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
                    let parameter = parameter.ok_or_else(|| {
                        self.unsupported(span, "束縛変数以外を先頭とするドット式")
                    })?;
                    self.source(first.span, parameter)?;
                    if parts.len() > 1
                        && !matches!(ty, Type::Z | Type::Bool | Type::Ref(_) | Type::Owned(_, _))
                    {
                        return Err(self.unsupported(span, "Z/Bool/Ref 以外の原始 slot 評価"));
                    }
                }
                ExprKind::Field { base, .. } => {
                    let owner = self.prepare_source(*base)?;
                    if !matches!(owner.known_value, Some(Scalar::Subject { .. })) {
                        return Err(self.unsupported(span, "未確定の参照からの field 読取り"));
                    }
                    if !matches!(ty, Type::Z | Type::Bool | Type::Ref(_) | Type::Owned(_, _)) {
                        return Err(self.unsupported(span, "Z/Bool/Ref 以外の原始 slot 評価"));
                    }
                }
                ExprKind::Group(child) => {
                    self.prepare_source(*child)?;
                }
                ExprKind::Unary {
                    op: UnOp::Neg,
                    operand,
                } if ty == Type::Z => {
                    self.prepare_source(*operand)?;
                }
                ExprKind::Binary { op, lhs, rhs }
                    if matches!(
                        op,
                        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                    ) =>
                {
                    let input_ty = self
                        .environment
                        .inputs
                        .law()
                        .expr_type(*lhs)
                        .ok_or_else(|| Failure::Internal("比較の型".into()))?;
                    if input_ty != &Type::Z
                        && !(input_ty == &Type::Bool && matches!(op, BinOp::Eq | BinOp::Ne))
                    {
                        return Err(self.unsupported(span, "Z/Bool 以外の比較"));
                    }
                    self.prepare_source(*lhs)?;
                    self.prepare_source(*rhs)?;
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
        let scope = source.scope;
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
            evidence: vec![],
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
            ExprKind::Int(n) if ty == Type::Z => {
                let v = self.value(
                    Scalar::Z(
                        n.parse()
                            .map_err(|_| Failure::Internal("整数 literal".into()))?,
                    ),
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
                let Some(binding) = found else {
                    return Err(self.unsupported(span, "束縛変数以外を先頭とするドット式"));
                };
                // 先頭 parameter の実在 token も独立した出現として残す。
                let mut current = self.finish(
                    first.span,
                    binding.ty.clone(),
                    Some(binding.value),
                    vec![],
                    self.graph.get(binding.value)?.support.clone(),
                    None,
                    None,
                    None,
                )?;
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
            ExprKind::Group(child) => {
                let child = self.eval(*child)?;
                self.finish(span, ty, child.value, vec![child], vec![], None, None, None)
            }
            ExprKind::Unary {
                op: UnOp::Neg,
                operand,
            } if ty == Type::Z => {
                let operand = self.eval(*operand)?;
                let value = match operand.value {
                    Some(r) => {
                        let Scalar::Z(v) = self.graph.scalar(r)? else {
                            return Err(Failure::Internal("負号の型".into()));
                        };
                        Some(self.value(
                            Scalar::Z(-v),
                            Rule::Input {
                                kind: "law",
                                location: Location::Law { span },
                            },
                            vec![r],
                            operand.support.clone(),
                            operand.scope.clone(),
                        )?)
                    }
                    None => None,
                };
                self.finish(span, ty, value, vec![operand], vec![], None, None, None)
            }
            ExprKind::Binary { op, lhs, rhs }
                if matches!(
                    op,
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                ) =>
            {
                let input_ty = self
                    .environment
                    .inputs
                    .law()
                    .expr_type(*lhs)
                    .ok_or_else(|| Failure::Internal("比較の型".into()))?;
                if input_ty != &Type::Z
                    && !(input_ty == &Type::Bool && matches!(op, BinOp::Eq | BinOp::Ne))
                {
                    return Err(self.unsupported(span, "Z/Bool 以外の比較"));
                }
                let left = self.eval(*lhs)?;
                let right = self.eval(*rhs)?;
                let mut scope = left.scope.clone();
                scope.merge(&right.scope);
                let mut support = left.support.clone();
                support.extend(right.support.iter().cloned());
                support.sort();
                support.dedup();
                let comparison = left.value.zip(right.value);
                let value = if let Some((l, r)) = comparison {
                    Some(self.value(
                        binary(*op, self.graph.scalar(l)?, self.graph.scalar(r)?)?,
                        Rule::Input {
                            kind: "law",
                            location: Location::Law { span },
                        },
                        vec![l, r],
                        support.clone(),
                        scope.clone(),
                    )?)
                } else {
                    None
                };
                let residual = if *op == BinOp::Eq && input_ty == &Type::Z {
                    if let Some((l, r)) = comparison {
                        let (Scalar::Z(a), Scalar::Z(b)) =
                            (self.graph.scalar(l)?, self.graph.scalar(r)?)
                        else {
                            return Err(Failure::Internal("等式残差の型".into()));
                        };
                        Some(self.value(
                            Scalar::Z(a - b),
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
            _ => Err(self.unsupported(span, format!("式形 {:?}", expr.kind))),
        }
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
        } = self.graph.scalar(reference)?.clone()
        else {
            return Err(self.unsupported(span, "原始 Ref 以外の field 読取り"));
        };
        let s = self.environment.subject(&snapshot, &subject)?;
        if s.ty != entity {
            return Err(Failure::Internal("field owner 型が合わない".into()));
        }
        let fullname = format!("{entity}.{name}");
        let field = self.environment.field(&s.snapshot, &s.id, &fullname)?;
        if !matches!(
            field.ty,
            Type::Z | Type::Bool | Type::Ref(_) | Type::Owned(_, _)
        ) {
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
                let value = scalar_from(value, &field.ty)
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
        if let Some(g) = &guard {
            match g.value.map(|r| self.graph.scalar(r)).transpose()? {
                Some(Scalar::Bool(true)) => {}
                _ => {
                    return Err(
                        self.unsupported(self.declaration.span, "false/未観測 guard の適用判定")
                    );
                }
            }
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
        // 明示 guard の適用評価。parts は実在する guard/body の各出現へ戻る。
        let evaluation = if let Some(g) = &guard {
            self.push(Node {
                ty: NodeType::Evaluation(Type::Bool),
                payload: Some(Payload::Evaluation {
                    expression: body.expression,
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
                    value: body.value,
                    applicability: "applicable",
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
        let decision = match body.value.map(|r| self.graph.scalar(r)).transpose()? {
            Some(Scalar::Bool(true)) => Decision::Established,
            Some(Scalar::Bool(false)) => Decision::Refuted,
            None => Decision::Undetermined,
            _ => return Err(Failure::Internal("Law body が Bool でない".into())),
        };
        let mut evidence = Vec::new();
        if let Some(value) = body.value {
            let (left, right) = match body.comparison {
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
                    residual: body.residual,
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
    let mut graph = Graph::new(control);
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
            let mut evaluator = Evaluator {
                environment,
                graph: &mut graph,
                control,
                request,
                declaration,
                bindings: vec![],
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
                evaluator
                    .graph
                    .validate_answer(&a, request.kind == QuestionKind::Check)?;
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
        answers,
        issues,
        status,
    })
}

#[cfg(test)]
mod recheck_tests {
    use super::*;
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
}
