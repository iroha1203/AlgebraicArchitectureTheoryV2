//! 明示束縛の参照・原始 field・Z/Bool literal・整数比較を原 AST から評価する。
use super::{
    PreparedObserved,
    control::{Checkpoint, Control, StopReason},
    environment::{Environment, binary, scalar_from},
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
struct Evaluator<'a, 'b> {
    environment: &'a Environment<'a>,
    graph: &'b mut Graph,
    control: &'b mut Control,
    request: &'a Request,
    declaration: &'a Declaration,
    bindings: Vec<Binding>,
    base: Scope,
    reasons: Vec<Reason>,
    completed: BTreeMap<ExprId, Evaluated>,
}
impl Evaluator<'_, '_> {
    fn tick(&mut self, point: Checkpoint) -> Result<(), Failure> {
        self.control.checkpoint(point).map_err(Failure::Stop)
    }
    fn push(&mut self, node: Node) -> Result<NodeRef, Failure> {
        self.environment.validate(self.graph, &node)?;
        self.graph.push(node).map_err(Failure::from)
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
    fn source(&mut self, span: (usize, usize), ty: Type, scope: Scope) -> Result<NodeRef, Failure> {
        self.push(Node {
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
            scope,
            reasons: vec![],
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
        let mut scope = self.base.clone();
        if let Some(value) = value {
            scope.merge(&self.graph.get(value)?.scope);
        }
        let mut support = own_support;
        let mut reasons = Vec::new();
        for child in &children {
            self.tick(Checkpoint::FiniteIteration)?;
            scope.merge(&child.scope);
            support.extend(child.support.iter().cloned());
            reasons.extend(child.reasons.iter().cloned());
            self.tick(Checkpoint::FiniteIteration)?;
        }
        if missing.is_some() {
            scope.completions = true;
        }
        support.sort();
        support.dedup();
        let expression = self.source(span, ty.clone(), scope.clone())?;
        if let Some(f) = missing {
            let reason = Reason {
                kind: ReasonKind::Missing,
                request: self.request.id.clone(),
                dependencies: vec![expression],
                missing: vec![f],
                location: Some(Location::Law { span }),
            };
            self.reasons.push(reason.clone());
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
            arguments: std::iter::once(body.expression)
                .chain(guard.as_ref().map(|g| g.expression))
                .chain(self.bindings.iter().map(|b| b.value))
                .collect(),
            support: body.support.clone(),
            evidence: vec![],
            judgment: None,
            scope: scope.clone(),
            reasons: vec![],
        })?;
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
                arguments: vec![instance, body.evaluation],
                support: body.support.clone(),
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
                        facts: body.support.clone(),
                    }),
                    rule: Rule::Construction("evidence"),
                    arguments: vec![instance, body.evaluation],
                    support: body.support.clone(),
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
            arguments: vec![instance, body.evaluation],
            support: body.support,
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
                reasons: vec![],
                completed: BTreeMap::new(),
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
                    // 表示の finalize。停止前に完成した root Evaluation/値だけを移す。
                    if let Some(completed) = evaluator.completed.get(&body) {
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
}
