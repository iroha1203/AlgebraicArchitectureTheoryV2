//! 不変の原始観測表からの参照・slot 読取りと、生成 leaf の元入力照合。
use super::{
    control::{Checkpoint, Control, StopReason},
    input::CheckedInputs,
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::{
    archmap::{Slot, Subject, Value},
    issue::Location,
    law::ast::{BinOp, ExprKind, UnOp},
    types::Type,
};
use std::collections::BTreeMap;

/// 入力照合中の metadata。Source の commit までは結果の理由へ昇格しない。
#[derive(Clone, Debug)]
pub(crate) struct PendingMissing {
    pub fact: Fact,
}
#[derive(Clone, Debug)]
pub(crate) struct SourceAnalysis {
    pub scope: Scope,
    pub known_value: Option<Scalar>,
    pub missing: Option<PendingMissing>,
    pub support: Vec<Fact>,
    pub scalar_scope: Option<Scope>,
}

struct SourceValue {
    scope: Scope,
    known_value: Option<Scalar>,
    support: Vec<Fact>,
    scalar_scope: Option<Scope>,
}

pub(crate) struct Environment<'a> {
    pub inputs: &'a CheckedInputs,
    subjects: BTreeMap<(String, String), &'a Subject>,
    fields: BTreeMap<(String, String, String), &'a crate::archmap::Field>,
    atoms: BTreeMap<String, Fact>,
    modes: BTreeMap<String, &'static str>,
    snapshot_origins: BTreeMap<String, String>,
    expressions: BTreeMap<(usize, usize), usize>,
    control: Control,
}
impl<'a> Environment<'a> {
    pub fn new(inputs: &'a CheckedInputs, control: &mut Control) -> Result<Self, StopReason> {
        let mut subjects = BTreeMap::new();
        let mut fields = BTreeMap::new();
        let mut atoms = BTreeMap::new();
        let mut modes = BTreeMap::new();
        let mut snapshot_origins = BTreeMap::new();
        let mut expressions = BTreeMap::new();
        for origin in &inputs.archmap().origins {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            modes.insert(origin.id.clone(), origin.mode.wire());
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        for (id, e) in inputs.law().exprs.iter().enumerate() {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            if inputs.law().expr_type(id).is_some() {
                expressions.insert(e.span, id);
            }
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        control.checkpoint(Checkpoint::FiniteIteration)?;
        for snapshot in &inputs.archmap().snapshots {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            snapshot_origins.insert(snapshot.id.clone(), snapshot.origin.clone());
            for s in &snapshot.subjects {
                control.checkpoint(Checkpoint::FiniteIteration)?;
                subjects.insert((s.snapshot.clone(), s.id.clone()), s);
                for field in &s.fields {
                    control.checkpoint(Checkpoint::FiniteIteration)?;
                    fields.insert(
                        (s.snapshot.clone(), s.id.clone(), field.name.clone()),
                        field,
                    );
                    if let Slot::Known { atom, pointer, .. } = &field.slot {
                        atoms.insert(
                            pointer.clone(),
                            Fact {
                                snapshot: s.snapshot.clone(),
                                subject: s.id.clone(),
                                field: Some(field.name.clone()),
                                atom: Some(atom.clone()),
                            },
                        );
                    }
                    control.checkpoint(Checkpoint::FiniteIteration)?;
                }
                control.checkpoint(Checkpoint::FiniteIteration)?;
            }
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        control.checkpoint(Checkpoint::FiniteIteration)?;
        Ok(Self {
            inputs,
            subjects,
            fields,
            atoms,
            modes,
            snapshot_origins,
            expressions,
            control: control.clone(),
        })
    }
    pub fn subject(&self, snapshot: &str, id: &str) -> Result<&'a Subject, String> {
        self.subjects
            .get(&(snapshot.into(), id.into()))
            .copied()
            .ok_or_else(|| "検査済み subject が見つからない".into())
    }
    pub fn origin_mode(&self, id: &str) -> Result<&'static str, String> {
        self.modes
            .get(id)
            .copied()
            .ok_or_else(|| "origin が見つからない".into())
    }
    pub fn field(
        &self,
        snapshot: &str,
        subject: &str,
        name: &str,
    ) -> Result<&'a crate::archmap::Field, String> {
        self.fields
            .get(&(snapshot.into(), subject.into(), name.into()))
            .copied()
            .ok_or_else(|| "field がない".into())
    }
    fn tick(&self) -> Result<(), ValidationFailure> {
        self.control
            .clone()
            .checkpoint(Checkpoint::FiniteIteration)
            .map_err(ValidationFailure::Stop)
    }
    pub fn scope(
        &self,
        s: &Subject,
        reading: &str,
        atom_origin: Option<&str>,
    ) -> Result<Scope, String> {
        let mut scope = Scope::default();
        scope.readings.insert(reading.into());
        scope.snapshots.insert(s.snapshot.clone());
        scope.modes.insert(self.origin_mode(&s.origin)?.into());
        let origin = self
            .snapshot_origins
            .get(&s.snapshot)
            .ok_or("snapshot がない")?;
        scope.modes.insert(self.origin_mode(origin)?.into());
        if let Some(origin) = atom_origin {
            scope.modes.insert(self.origin_mode(origin)?.into());
        }
        Ok(scope)
    }
    pub fn fact(&self, f: &Fact) -> Result<(), String> {
        let s = self.subject(&f.snapshot, &f.subject)?;
        match (&f.field, &f.atom) {
            (None, None) => Ok(()),
            (Some(field), atom) => {
                let field = self.field(&s.snapshot, &s.id, field)?;
                match (&field.slot, atom) {
                    (Slot::Missing, None) => Ok(()),
                    (Slot::Known { atom: a, .. }, Some(b)) if a == b => Ok(()),
                    _ => Err("FactPointer が原始 slot と合わない".into()),
                }
            }
            _ => Err("subject 存在に atom が付いている".into()),
        }
    }
    pub fn validate(&self, graph: &Graph, node: &Node) -> Result<(), ValidationFailure> {
        self.tick()?;
        for f in &node.support {
            self.tick()?;
            self.fact(f)?;
            if f.field.is_some() && f.atom.is_none() {
                return Err("未観測 slot を support Atom にしている".into());
            }
            self.tick()?;
        }
        for reason in &node.reasons {
            self.tick()?;
            for f in &reason.missing {
                self.tick()?;
                self.fact(f)?;
                self.tick()?;
            }
            self.tick()?;
        }
        if let Some(Payload::Scalar(scalar)) = &node.payload {
            match &node.rule {
                Rule::Input {
                    kind: "subject",
                    location: Location::ArchMap { pointer, .. },
                } => {
                    let Scalar::Subject {
                        snapshot,
                        subject,
                        entity,
                    } = scalar
                    else {
                        return Err("subject leaf の値が参照でない".into());
                    };
                    let s = self.subject(snapshot, subject)?;
                    if pointer != &s.pointer || entity != &s.ty {
                        return Err("subject leaf が原入力に合わない".into());
                    }
                }
                Rule::Input {
                    kind: "atom",
                    location: Location::ArchMap { pointer, .. },
                } => {
                    let mut found = false;
                    for f in &node.support {
                        self.tick()?;
                        if f.atom.is_some() {
                            let subject = self.subject(&f.snapshot, &f.subject)?;
                            let field = self.field(
                                &subject.snapshot,
                                &subject.id,
                                f.field.as_ref().ok_or("atom field がない")?,
                            )?;
                            if let Slot::Known {
                                value, pointer: p, ..
                            } = &field.slot
                                && p == pointer
                                && scalar_from(value, &field.ty).as_ref() == Some(scalar)
                            {
                                found = true;
                            }
                        }
                        self.tick()?;
                    }
                    if !found {
                        return Err("Atom 値が元 slot に合わない".into());
                    }
                }
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                } => {
                    let law = self.inputs.law();
                    let id = *self.expressions.get(span).ok_or("原 AST がない")?;
                    let expr = (id, &law.exprs[id]);
                    if law.expr_type(expr.0) != Some(&scalar.ty()) {
                        return Err("導出値が元式の型に合わない".into());
                    }
                    let computed = match &expr.1.kind {
                        ExprKind::Int(n) => {
                            Scalar::Z(n.parse().map_err(|_| "整数 literal の内部不整合")?)
                        }
                        ExprKind::Bool(b) => Scalar::Bool(*b),
                        ExprKind::Binary { op, .. } => {
                            if node.arguments.len() != 2 {
                                return Err("二項演算の引数数".into());
                            }
                            binary(
                                *op,
                                graph.scalar(node.arguments[0])?,
                                graph.scalar(node.arguments[1])?,
                            )?
                        }
                        ExprKind::Unary { op: UnOp::Neg, .. } => {
                            if node.arguments.len() != 1 {
                                return Err("負号の引数数".into());
                            }
                            let Scalar::Z(v) = graph.scalar(node.arguments[0])? else {
                                return Err("負号が整数でない".into());
                            };
                            Scalar::Z(-v)
                        }
                        _ => return Err("元式に対する値検査がない".into()),
                    };
                    if &computed != scalar {
                        return Err("生成算術が元式に合わない".into());
                    }
                }
                Rule::Construction("proposition")
                    if scalar == &Scalar::Bool(true) && node.arguments.len() == 1 =>
                {
                    graph.expect(node.arguments[0], &NodeType::LawInstance)?
                }
                Rule::Construction("evaluation") => {
                    if node.arguments.len() != 2 {
                        return Err("残差の引数数".into());
                    }
                    let (Scalar::Z(l), Scalar::Z(r), Scalar::Z(d)) = (
                        graph.scalar(node.arguments[0])?,
                        graph.scalar(node.arguments[1])?,
                        scalar,
                    ) else {
                        return Err("残差が整数でない".into());
                    };
                    if l - r != *d {
                        return Err("残差再検査失敗".into());
                    }
                }
                _ => return Err("値 leaf の導出規則がない".into()),
            }
            let support = self.scalar_support(graph, node, graph.nodes.len())?;
            if node.support != support {
                return Err("値の支持が元入力・実引数の完全な集合と違う".into());
            }
        }
        if let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &node.payload
        {
            let bytes = self.inputs.sources().law().bytes();
            if span.0 >= span.1 || bytes.get(span.0..span.1).is_none() {
                return Err("元 byte span の外".into());
            }
            let actual = self
                .expressions
                .get(span)
                .map(|&id| (id, &self.inputs.law().exprs[id]));
            if let Some((id, _)) = actual {
                let NodeType::Expression(ty) = &node.ty else {
                    return Err("式の型".into());
                };
                if self.inputs.law().expr_type(id) != Some(ty) {
                    return Err("Expression の型が元 AST に合わない".into());
                }
            } else {
                // Dotted の先頭 parameter と射影途中は実在 token の半開区間。
                let source = std::str::from_utf8(&bytes[span.0..span.1])
                    .map_err(|_| "式 token が UTF-8 でない")?;
                let Some(Payload::Expression { bindings, .. }) = &node.payload else {
                    unreachable!()
                };
                let mut found = false;
                for binding in bindings {
                    self.tick()?;
                    found |= binding.name == source;
                    self.tick()?;
                }
                if !found {
                    return Err("元 AST にない式 fragment".into());
                }
            }
        }
        if let Some(Payload::Expression {
            location: Location::Law { span },
            bindings,
            ..
        }) = &node.payload
            && node.scope != self.source_scope(graph, *span, bindings)?
        {
            return Err("Expression の範囲が元宣言・入力と違う".into());
        }
        if let Some(Payload::LawInstance {
            name,
            role,
            bindings,
            guard,
            body,
            occurrence,
        }) = &node.payload
        {
            use crate::law::{ast::Role, model::Signature};
            let d = self
                .inputs
                .law()
                .declarations
                .get(name)
                .ok_or("LawInstance の宣言がない")?;
            let Signature::Law {
                role: r,
                params,
                guard: g,
                body: b,
            } = &d.signature
            else {
                return Err("LawInstance が Law でない".into());
            };
            if role
                != &match r {
                    Role::Required => "required",
                    Role::Optional => "optional",
                }
                || occurrence != &(Location::Law { span: d.span })
            {
                return Err("LawInstance の宣言 metadata 不一致".into());
            }
            if params.len() != bindings.len() {
                return Err("LawInstance の未束縛 parameter".into());
            }
            for (p, b) in params.iter().zip(bindings) {
                self.tick()?;
                if p.name != b.name || p.ty.erase() != b.ty {
                    return Err("LawInstance の束縛署名不一致".into());
                }
                self.tick()?;
            }
            self.source_matches(graph, *body, *b)?;
            match (guard, g) {
                (Some(v), Some(e)) => self.source_matches(graph, *v, *e)?,
                (None, None) => {}
                _ => return Err("guard の出現不一致".into()),
            }
            self.application(graph, node)?;
        }
        if let Some(Payload::Evaluation {
            expression,
            bindings,
            parts,
            value,
            ..
        }) = &node.payload
        {
            let application = node
                .arguments
                .first()
                .copied()
                .filter(|r| matches!(graph.get(*r).map(|n| &n.ty), Ok(NodeType::LawInstance)));
            if let Some(instance) = application {
                self.validate_law_evaluation(graph, node, instance)?;
            } else {
                let span = self.expression_span(graph, *expression)?;
                let source_bindings = self.expression_bindings(graph, *expression)?;
                if source_bindings != bindings
                    || parts.len() != 1
                    || parts[0].location != (Location::Law { span })
                    || parts[0].value != *value
                {
                    return Err("Evaluation の原式・束縛・part が合わない".into());
                }
                let analysis = self.analyze_source(graph, span, bindings)?;
                let expected_scope = analysis.scope;
                if node.scope != expected_scope || graph.get(*expression)?.scope != expected_scope {
                    return Err("Evaluation と元式の範囲が元入力と違う".into());
                }
                if node.support != analysis.support {
                    return Err("Evaluation の支持が元 AST・原始事実の完全な集合と違う".into());
                }
                let mut used_support = Vec::new();
                if let Some(reference) = value {
                    let expected = analysis
                        .scalar_scope
                        .as_ref()
                        .ok_or("元式に確定値の範囲がない")?;
                    if &graph.get(*reference)?.scope != expected {
                        return Err("評価値Scalarの範囲が元Source・束縛・originと違う".into());
                    }
                    used_support.extend(graph.get(*reference)?.support.iter().cloned());
                }
                let children = &parts[0].children;
                for &child in children {
                    self.tick()?;
                    used_support.extend(graph.get(child)?.support.iter().cloned());
                    self.tick()?;
                }
                used_support.sort();
                used_support.dedup();
                if node.support != used_support {
                    return Err("Evaluation の支持が使用した値・子評価の和集合と違う".into());
                }
                let children = &parts[0].children;
                let ast = self
                    .expressions
                    .get(&span)
                    .map(|id| &self.inputs.law().exprs[*id]);
                let expected = match ast.map(|e| &e.kind) {
                    Some(ExprKind::Binary { lhs, rhs, .. }) => vec![
                        self.inputs.law().exprs[*lhs].span,
                        self.inputs.law().exprs[*rhs].span,
                    ],
                    Some(ExprKind::Unary { operand, .. } | ExprKind::Group(operand)) => {
                        vec![self.inputs.law().exprs[*operand].span]
                    }
                    Some(ExprKind::Field { base, .. }) => vec![self.inputs.law().exprs[*base].span],
                    Some(ExprKind::Dotted(parts)) if parts.len() > 1 => {
                        vec![(parts[0].span.0, parts[parts.len() - 2].span.1)]
                    }
                    _ => vec![],
                };
                if children.len() != expected.len() {
                    return Err("元 AST と子 Evaluation の個数不一致".into());
                }
                let mut child_values = Vec::new();
                for (&child, expected_span) in children.iter().zip(expected) {
                    self.tick()?;
                    let (e, b, v) = self.evaluation(graph, child)?;
                    if self.expression_span(graph, e)? != expected_span || b != bindings {
                        return Err("元 AST の子出現・束縛不一致".into());
                    }
                    child_values.push(v);
                    self.tick()?;
                }
                if !matches!(ast.map(|e| &e.kind), Some(ExprKind::Binary { .. }))
                    && parts[0].residual.is_some()
                {
                    return Err("比較以外の式に残差がある".into());
                }
                match ast.map(|e| &e.kind) {
                    Some(ExprKind::Int(n)) => {
                        let expected = Scalar::Z(n.parse().map_err(|_| "元整数 literal が不正")?);
                        if value.map(|r| graph.scalar(r)).transpose()? != Some(&expected) {
                            return Err("整数 literal の評価値が元 AST と違う".into());
                        }
                    }
                    Some(ExprKind::Bool(b)) => {
                        if value.map(|r| graph.scalar(r)).transpose()? != Some(&Scalar::Bool(*b)) {
                            return Err("Bool literal の評価値が元 AST と違う".into());
                        }
                    }
                    Some(ExprKind::Binary { op, lhs, .. }) => {
                        let pair = child_values[0].zip(child_values[1]);
                        match (pair, *value) {
                            (Some((left, right)), Some(result)) => {
                                if graph.scalar(result)?
                                    != &binary(*op, graph.scalar(left)?, graph.scalar(right)?)?
                                    || graph.get(result)?.arguments != [left, right]
                                {
                                    return Err("生成比較値の元左右が違う".into());
                                }
                            }
                            (None, None) => {}
                            _ => return Err("未確定の子からの比較値生成".into()),
                        }
                        match (op, pair, parts[0].residual) {
                            (BinOp::Eq, Some((left, right)), residual)
                                if self.inputs.law().expr_type(*lhs) == Some(&Type::Z)
                                    && matches!(
                                        (graph.scalar(left)?, graph.scalar(right)?),
                                        (Scalar::Z(_), Scalar::Z(_))
                                    ) =>
                            {
                                let residual = residual.ok_or("既知 Z 等号の残差がない")?;
                                graph.expect(residual, &NodeType::Value(Type::Z))?;
                                if graph.get(residual)?.scope != expected_scope {
                                    return Err("Z等号残差Scalarの範囲が元等式と違う".into());
                                }
                                let (Scalar::Z(l), Scalar::Z(r), Scalar::Z(d)) = (
                                    graph.scalar(left)?,
                                    graph.scalar(right)?,
                                    graph.scalar(residual)?,
                                ) else {
                                    return Err("Z 等号残差の型が違う".into());
                                };
                                if l - r != *d || graph.get(residual)?.arguments != [left, right] {
                                    return Err("Z 等号の残差が元左右の正確な差でない".into());
                                }
                                self.validate(graph, graph.get(residual)?)?;
                            }
                            (_, _, None) => {}
                            _ => return Err("Z 等号の既知左右以外に整数残差がある".into()),
                        }
                    }
                    Some(ExprKind::Group(_)) => {
                        if *value != child_values[0] {
                            return Err("括弧の評価値不一致".into());
                        }
                    }
                    Some(ExprKind::Unary { op: UnOp::Neg, .. }) => {
                        match (child_values[0], *value) {
                            (Some(operand), Some(result)) => {
                                let Scalar::Z(n) = graph.scalar(operand)? else {
                                    return Err("負号の元 operand が整数でない".into());
                                };
                                if graph.scalar(result)? != &Scalar::Z(-n)
                                    || graph.get(result)?.arguments != [operand]
                                {
                                    return Err("負号の元 operand・結果値が違う".into());
                                }
                            }
                            (None, None) => {}
                            _ => return Err("負号の子値と結果値の有無が違う".into()),
                        }
                    }
                    Some(ExprKind::Dotted(parts)) => {
                        if parts.len() == 1 {
                            self.check_parameter(graph, bindings, &parts[0].name, *value)?;
                        } else {
                            self.check_field(
                                graph,
                                child_values[0],
                                &parts[parts.len() - 1].name,
                                *value,
                            )?;
                        }
                    }
                    Some(ExprKind::Field { name, .. }) => {
                        self.check_field(graph, child_values[0], &name.name, *value)?
                    }
                    None => {
                        let source = std::str::from_utf8(
                            &self.inputs.sources().law().bytes()[span.0..span.1],
                        )
                        .map_err(|_| "parameter token")?;
                        self.check_parameter(graph, bindings, source, *value)?;
                    }
                    _ => {}
                }
            }
        }
        match &node.payload {
            Some(Payload::EvaluationEvidence {
                instance,
                lhs,
                rhs,
                residual,
            }) => {
                let (evaluation, left, right) = self.evidence_operands(graph, node, *instance)?;
                if *lhs != left || *rhs != right {
                    return Err("評価証拠が元の左右値を指していない".into());
                }
                let Some(Payload::Evaluation { parts, .. }) = &graph.get(evaluation)?.payload
                else {
                    unreachable!()
                };
                if *residual != parts.last().ok_or("証拠の評価 part がない")?.residual {
                    return Err("証拠の残差が元評価と違う".into());
                }
            }
            Some(Payload::Counterexample {
                bindings,
                left,
                right,
                facts,
            }) => {
                let instance = *node.arguments.first().ok_or("反例に LawInstance がない")?;
                let (evaluation, l, r) = self.evidence_operands(graph, node, instance)?;
                if *left != l || *right != r {
                    return Err("反例が元式の左右値を指していない".into());
                }
                let (_, bs, v) = self.evaluation(graph, evaluation)?;
                if bs != bindings
                    || v.map(|r| graph.scalar(r)).transpose()? != Some(&Scalar::Bool(false))
                {
                    return Err("反例の元束縛・false 評価不一致".into());
                }
                if facts != &graph.get(evaluation)?.support {
                    return Err("反例 facts が元評価と違う".into());
                }
                for fact in facts {
                    self.tick()?;
                    self.fact(fact)?;
                    self.tick()?;
                }
            }
            Some(Payload::Proposition { instance }) => {
                graph.validate_proposition_evidence(node)?;
                for &reference in &node.evidence {
                    self.tick()?;
                    self.validate(graph, graph.get(reference)?)?;
                    self.tick()?;
                }
                let evaluation = *node.arguments.get(1).ok_or("命題に元評価がない")?;
                self.instance_evaluation(graph, *instance, evaluation)?;
                let (_, _, v) = self.evaluation(graph, evaluation)?;
                let status = match v.map(|r| graph.scalar(r)).transpose()? {
                    Some(Scalar::Bool(true)) => Decision::Established,
                    Some(Scalar::Bool(false)) => Decision::Refuted,
                    None => Decision::Undetermined,
                    _ => return Err("命題 body の型".into()),
                };
                if node.judgment.as_ref().map(|j| j.status) != Some(status) {
                    return Err("命題判断が元 body と違う".into());
                }
            }
            _ => {}
        }
        if matches!(
            node.payload,
            Some(
                Payload::EvaluationEvidence { .. }
                    | Payload::Counterexample { .. }
                    | Payload::Proposition { .. }
            )
        ) {
            let evaluation = *node.arguments.get(1).ok_or("結論に適用評価がない")?;
            if node.support != graph.get(evaluation)?.support
                || node.scope != graph.get(evaluation)?.scope
            {
                return Err("結論の支持・範囲が適用評価と合わない".into());
            }
        }
        self.tick()?;
        Ok(())
    }
    // Scalar の支持も自己申告の集合を信じず、原始 leaf または実引数から復元する。
    fn scalar_support(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<Vec<Fact>, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            let Some(Payload::Scalar(value)) = &node.payload else {
                return Err("支持の依存先が通常値でない".into());
            };
            for reference in &node.arguments {
                self.tick()?;
                if reference.0 >= limit {
                    return Err("値支持の引数が既出でない".into());
                }
                self.tick()?;
            }
            let mut support = match &node.rule {
                Rule::Input {
                    kind: "subject",
                    location: Location::ArchMap { pointer, .. },
                } => {
                    let Scalar::Subject {
                        snapshot,
                        subject,
                        entity,
                    } = value
                    else {
                        return Err("subject支持の値型".into());
                    };
                    let actual = self.subject(snapshot, subject)?;
                    if actual.pointer != *pointer
                        || actual.ty != *entity
                        || !node.arguments.is_empty()
                    {
                        return Err("subject支持の元入力不一致".into());
                    }
                    self.subject_support(value)?
                }
                Rule::Input {
                    kind: "atom",
                    location: Location::ArchMap { pointer, .. },
                } => {
                    let fact = self
                        .atoms
                        .get(pointer)
                        .ok_or("Atom支持の元入力位置がない")?;
                    let field = self.field(
                        &fact.snapshot,
                        &fact.subject,
                        fact.field.as_ref().ok_or("Atom fieldがない")?,
                    )?;
                    let Slot::Known { value: actual, .. } = &field.slot else {
                        return Err("Atom支持が欠測slotを指す".into());
                    };
                    if scalar_from(actual, &field.ty).as_ref() != Some(value)
                        || node.arguments.len() != 1
                    {
                        return Err("Atom支持の原始値・owner引数数が違う".into());
                    }
                    let Scalar::Subject {
                        snapshot, subject, ..
                    } = graph.scalar(node.arguments[0])?
                    else {
                        return Err("Atom支持のownerがRefでない".into());
                    };
                    if snapshot != &fact.snapshot || subject != &fact.subject {
                        return Err("Atom支持のowner identity不一致".into());
                    }
                    vec![fact.clone()]
                }
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                } => {
                    let expr = &self.inputs.law().exprs
                        [*self.expressions.get(span).ok_or("値支持の元ASTがない")?];
                    match expr.kind {
                        ExprKind::Int(_) | ExprKind::Bool(_) => {
                            if !node.arguments.is_empty() {
                                return Err("literalに引数支持がある".into());
                            }
                            vec![]
                        }
                        ExprKind::Binary { .. } | ExprKind::Unary { .. } => {
                            self.argument_support(graph, &node.arguments, limit)?
                        }
                        _ => return Err("値支持の未実装元式".into()),
                    }
                }
                Rule::Construction("evaluation") => {
                    self.argument_support(graph, &node.arguments, limit)?
                }
                Rule::Construction("proposition") => vec![],
                _ => return Err("値支持の導出規則がない".into()),
            };
            support.sort();
            support.dedup();
            self.tick()?;
            Ok(support)
        })
    }
    fn argument_support(
        &self,
        graph: &Graph,
        arguments: &[NodeRef],
        limit: usize,
    ) -> Result<Vec<Fact>, ValidationFailure> {
        let mut support = Vec::new();
        for &reference in arguments {
            self.tick()?;
            if reference.0 >= limit {
                return Err("支持の引数が既出でない".into());
            }
            let node = graph.get(reference)?;
            let actual = self.scalar_support(graph, node, reference.0)?;
            if node.support != actual {
                return Err("引数値の支持が元入力から欠落・過剰".into());
            }
            support.extend(actual);
            // Atom 値の direct support は field 一件だが、その式を使うには owner の
            // 参照元も必要。中間 Ref field を含む owner 依存を意味に従って合流する。
            if matches!(&node.rule, Rule::Input { kind: "atom", .. }) {
                support.extend(self.argument_support(graph, &node.arguments, reference.0)?);
            }
            self.tick()?;
        }
        support.sort();
        support.dedup();
        Ok(support)
    }
    /// 完成 Answer の必須検査。構造検査と、元 Request への意味上の帰属を一緒に確かめる。
    pub(crate) fn validate_answer(
        &self,
        graph: &Graph,
        request: &Request,
        answer: &Answer,
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        graph.validate_answer(answer, request.kind == QuestionKind::Check)?;
        if answer.id != request.id {
            return Err("Answer ID が元Requestと違う".into());
        }
        let Selector::Declaration { name } = &request.head else {
            return Err("解決済みRequestのheadが宣言でない".into());
        };
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(name)
            .ok_or("Requestの元宣言がない")?;
        let (params, body) = match (&request.kind, &declaration.signature) {
            (QuestionKind::Evaluate, crate::law::model::Signature::View { params, body, .. }) => {
                (params, *body)
            }
            (QuestionKind::Check, crate::law::model::Signature::Law { params, body, .. }) => {
                (params, *body)
            }
            _ => return Err("Request種別と元宣言が違う".into()),
        };
        let evaluation = *answer
            .outputs
            .get("evaluation")
            .ok_or("完成Answerに元評価がない")?;
        let (expression, bindings, _) = self.evaluation(graph, evaluation)?;
        self.source_matches(graph, expression, body)?;
        self.recheck_evaluation(graph, evaluation)?;
        if bindings.len() != params.len() || request.arguments.len() != params.len() {
            return Err("Requestの明示束縛数がAnswerと違う".into());
        }
        for (parameter, binding) in params.iter().zip(bindings) {
            self.tick()?;
            if parameter.name != binding.name || parameter.ty.erase() != binding.ty {
                return Err("Requestのparameter署名がAnswerと違う".into());
            }
            let key = format!("bind.{}", parameter.name);
            let mut selected = None;
            for argument in &request.arguments {
                self.tick()?;
                if argument.name == key {
                    if selected.is_some() {
                        return Err("Requestの束縛名が重複".into());
                    }
                    selected = Some(&argument.value);
                }
                self.tick()?;
            }
            let Some(Selector::Subject { snapshot, subject }) = selected else {
                return Err("完成Answerの元明示subject束縛がない".into());
            };
            let Scalar::Subject {
                snapshot: actual_snapshot,
                subject: actual_subject,
                entity,
            } = graph.scalar(binding.value)?
            else {
                return Err("Answer束縛が通常のRef値でない".into());
            };
            if actual_snapshot != snapshot
                || actual_subject != subject
                || &self.subject(snapshot, subject)?.ty != entity
            {
                return Err("Answer束縛がRequestのsubject identityと違う".into());
            }
            self.tick()?;
        }
        if request.kind == QuestionKind::Check {
            let claim = answer.claim.ok_or("完成check Answerにclaimがない")?;
            let Some(Payload::Proposition { instance }) = &graph.get(claim)?.payload else {
                return Err("Requestのclaimが命題でない".into());
            };
            let Some(Payload::LawInstance {
                name: actual,
                bindings: instance_bindings,
                ..
            }) = &graph.get(*instance)?.payload
            else {
                return Err("RequestのclaimにLawInstanceがない".into());
            };
            if actual != name || instance_bindings != bindings {
                return Err("check AnswerのLawInstanceがRequestと違う".into());
            }
            self.instance_evaluation(graph, *instance, evaluation)?;
            self.validate(graph, graph.get(claim)?)?;
        }
        self.tick()?;
        Ok(())
    }
    // 自己申告の node.scope へ依存せず、元宣言・束縛と原始 slot から再構成する。
    fn source_scope(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<Scope, ValidationFailure> {
        self.analyze_source(graph, span, bindings)
            .map(|analysis| analysis.scope)
    }
    pub(crate) fn analyze_source(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<SourceAnalysis, ValidationFailure> {
        let mut declaration = None;
        for d in self.inputs.law().declarations.values() {
            self.tick()?;
            if d.span.0 <= span.0 && span.1 <= d.span.1 {
                if declaration.is_some() {
                    return Err("原式を所有する宣言が一意でない".into());
                }
                declaration = Some(d);
            }
            self.tick()?;
        }
        let declaration = declaration.ok_or("原式を所有する宣言がない")?;
        let params = match &declaration.signature {
            crate::law::model::Signature::View { params, .. }
            | crate::law::model::Signature::Law { params, .. } => params,
            _ => return Err("評価範囲の元宣言が view/Law でない".into()),
        };
        if params.len() != bindings.len() {
            return Err("評価範囲のparameter束縛数が違う".into());
        }
        let mut base = Scope::default();
        base.readings.insert(declaration.reading.clone());
        let mut variables = BTreeMap::new();
        for (parameter, binding) in params.iter().zip(bindings) {
            self.tick()?;
            if parameter.name != binding.name || parameter.ty.erase() != binding.ty {
                return Err("評価範囲の元parameter署名が違う".into());
            }
            let value = graph.scalar(binding.value)?;
            let Scalar::Subject {
                snapshot,
                subject,
                entity,
            } = value
            else {
                return Err("未実装の値parameterを評価範囲へ持ち込んでいる".into());
            };
            let actual = self.subject(snapshot, subject)?;
            if &actual.ty != entity || value.ty() != binding.ty {
                return Err("評価範囲の束縛subject型が違う".into());
            }
            let subject_scope = self.scope(actual, &declaration.reading, None)?;
            if graph.get(binding.value)?.scope != subject_scope {
                return Err("束縛subject値の範囲が元宣言・subject由来と違う".into());
            }
            base.merge(&subject_scope);
            variables.insert(binding.name.clone(), value.clone());
            self.tick()?;
        }
        if let Some(&id) = self.expressions.get(&span) {
            let SourceValue {
                scope,
                known_value,
                support,
                scalar_scope,
            } = self.scoped_ast(id, &variables, &base, &declaration.reading)?;
            let direct_field = match &self.inputs.law().exprs[id].kind {
                ExprKind::Dotted(parts) if parts.len() == 2 => Some((
                    variables.get(&parts[0].name).cloned(),
                    parts[1].name.as_str(),
                )),
                ExprKind::Field { base: owner, name } => Some((
                    self.scoped_ast(*owner, &variables, &base, &declaration.reading)?
                        .known_value,
                    name.name.as_str(),
                )),
                _ => None,
            };
            let missing = if let Some((
                Some(Scalar::Subject {
                    snapshot,
                    subject,
                    entity,
                }),
                name,
            )) = direct_field
            {
                let field = self.field(&snapshot, &subject, &format!("{entity}.{name}"))?;
                match &field.slot {
                    Slot::Missing => Some(PendingMissing {
                        fact: Fact {
                            snapshot,
                            subject,
                            field: Some(field.name.clone()),
                            atom: None,
                        },
                    }),
                    Slot::Known { .. } => None,
                }
            } else {
                None
            };
            return Ok(SourceAnalysis {
                scope,
                known_value,
                missing,
                support,
                scalar_scope,
            });
        }
        // Dotted の先頭 parameter は実在 token のみを指す。
        let token = self
            .inputs
            .sources()
            .law()
            .bytes()
            .get(span.0..span.1)
            .ok_or("評価範囲のtokenが元byte外")?;
        let name = std::str::from_utf8(token).map_err(|_| "評価範囲のtokenがUTF-8でない")?;
        if !variables.contains_key(name) {
            return Err("評価範囲に元parameter以外のfragmentがある".into());
        }
        let known_value = variables.get(name).cloned();
        let support = self.subject_support(known_value.as_ref().ok_or("元parameter値がない")?)?;
        let scalar_scope = Some(self.subject_scalar_scope(
            known_value.as_ref().ok_or("元parameter値がない")?,
            &declaration.reading,
        )?);
        Ok(SourceAnalysis {
            scope: base,
            known_value,
            missing: None,
            support,
            scalar_scope,
        })
    }
    fn subject_support(&self, value: &Scalar) -> Result<Vec<Fact>, ValidationFailure> {
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = value
        else {
            return Err("支持の元parameterがRefでない".into());
        };
        if self.subject(snapshot, subject)?.ty != *entity {
            return Err("支持の元subject型が違う".into());
        }
        Ok(vec![Fact {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field: None,
            atom: None,
        }])
    }
    fn subject_scalar_scope(
        &self,
        value: &Scalar,
        reading: &str,
    ) -> Result<Scope, ValidationFailure> {
        let Scalar::Subject {
            snapshot, subject, ..
        } = value
        else {
            return Err("subject値の範囲をRef以外へ適用".into());
        };
        Ok(self.scope(self.subject(snapshot, subject)?, reading, None)?)
    }
    fn scoped_ast(
        &self,
        id: usize,
        variables: &BTreeMap<String, Scalar>,
        base: &Scope,
        reading: &str,
    ) -> Result<SourceValue, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            let expression = &self.inputs.law().exprs[id];
            let result = match &expression.kind {
                ExprKind::Int(n) if self.inputs.law().expr_type(id) == Some(&Type::Z) => {
                    SourceValue {
                        scope: base.clone(),
                        known_value: Some(Scalar::Z(
                            n.parse().map_err(|_| "範囲検査の整数literal不正")?,
                        )),
                        support: vec![],
                        scalar_scope: Some(base.clone()),
                    }
                }
                ExprKind::Bool(b) => SourceValue {
                    scope: base.clone(),
                    known_value: Some(Scalar::Bool(*b)),
                    support: vec![],
                    scalar_scope: Some(base.clone()),
                },
                ExprKind::Dotted(parts) => {
                    let first = parts.first().ok_or("範囲検査の空Dotted")?;
                    let value = variables
                        .get(&first.name)
                        .ok_or("範囲検査の未知parameter")?
                        .clone();
                    let support = self.subject_support(&value)?;
                    let scalar_scope = Some(self.subject_scalar_scope(&value, reading)?);
                    let mut result = SourceValue {
                        scope: base.clone(),
                        known_value: Some(value),
                        support,
                        scalar_scope,
                    };
                    for part in parts.iter().skip(1) {
                        self.tick()?;
                        result = self.scoped_field(result, &part.name, base, reading)?;
                        self.tick()?;
                    }
                    result
                }
                ExprKind::Field { base: owner, name } => self.scoped_field(
                    self.scoped_ast(*owner, variables, base, reading)?,
                    &name.name,
                    base,
                    reading,
                )?,
                ExprKind::Group(child) => self.scoped_ast(*child, variables, base, reading)?,
                ExprKind::Unary {
                    op: UnOp::Neg,
                    operand,
                } => {
                    let SourceValue {
                        scope,
                        known_value,
                        support,
                        ..
                    } = self.scoped_ast(*operand, variables, base, reading)?;
                    let known_value = match known_value {
                        Some(Scalar::Z(v)) => Some(Scalar::Z(-v)),
                        None => None,
                        _ => return Err("範囲検査の負号型不一致".into()),
                    };
                    let scalar_scope = known_value.as_ref().map(|_| scope.clone());
                    SourceValue {
                        scope,
                        known_value,
                        support,
                        scalar_scope,
                    }
                }
                ExprKind::Binary { op, lhs, rhs } => {
                    let SourceValue {
                        mut scope,
                        known_value: left,
                        mut support,
                        ..
                    } = self.scoped_ast(*lhs, variables, base, reading)?;
                    let right = self.scoped_ast(*rhs, variables, base, reading)?;
                    scope.merge(&right.scope);
                    support.extend(right.support);
                    support.sort();
                    support.dedup();
                    let known_value = match (left, right.known_value) {
                        (Some(l), Some(r)) => Some(binary(*op, &l, &r)?),
                        _ => None,
                    };
                    let scalar_scope = known_value.as_ref().map(|_| scope.clone());
                    SourceValue {
                        scope,
                        known_value,
                        support,
                        scalar_scope,
                    }
                }
                _ => return Err("未実装式の範囲を自己申告から採用できない".into()),
            };
            self.tick()?;
            Ok(result)
        })
    }
    fn scoped_field(
        &self,
        base: SourceValue,
        name: &str,
        request_base: &Scope,
        reading: &str,
    ) -> Result<SourceValue, ValidationFailure> {
        let SourceValue {
            mut scope,
            known_value,
            mut support,
            ..
        } = base;
        let Some(Scalar::Subject {
            snapshot,
            subject,
            entity,
        }) = known_value
        else {
            return Err("範囲検査のfield ownerが未確定/Ref以外".into());
        };
        let owner = self.subject(&snapshot, &subject)?;
        if owner.ty != entity {
            return Err("範囲検査のfield owner型不一致".into());
        }
        let field = self.field(&snapshot, &subject, &format!("{entity}.{name}"))?;
        let (known_value, scalar_scope) = match &field.slot {
            Slot::Known {
                atom,
                origin,
                value,
                ..
            } => {
                let owner_scope = self.scope(owner, reading, Some(origin))?;
                scope.merge(&owner_scope);
                let mut scalar_scope = request_base.clone();
                scalar_scope.merge(&owner_scope);
                support.push(Fact {
                    snapshot,
                    subject,
                    field: Some(field.name.clone()),
                    atom: Some(atom.clone()),
                });
                (
                    Some(scalar_from(value, &field.ty).ok_or("範囲検査の未実装原始値")?),
                    Some(scalar_scope),
                )
            }
            Slot::Missing => {
                scope.merge(&self.scope(owner, reading, None)?);
                scope.completions = true;
                (None, None)
            }
        };
        support.sort();
        support.dedup();
        Ok(SourceValue {
            scope,
            known_value,
            support,
            scalar_scope,
        })
    }
    fn expression_span(&self, graph: &Graph, r: NodeRef) -> Result<(usize, usize), String> {
        match &graph.get(r)?.payload {
            Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) => Ok(*span),
            _ => Err("元式 span がない".into()),
        }
    }
    fn expression_bindings<'g>(
        &self,
        graph: &'g Graph,
        r: NodeRef,
    ) -> Result<&'g [Binding], String> {
        match &graph.get(r)?.payload {
            Some(Payload::Expression { bindings, .. }) => Ok(bindings),
            _ => Err("式束縛がない".into()),
        }
    }
    fn evaluation<'g>(
        &self,
        graph: &'g Graph,
        r: NodeRef,
    ) -> Result<(NodeRef, &'g [Binding], Option<NodeRef>), String> {
        match &graph.get(r)?.payload {
            Some(Payload::Evaluation {
                expression,
                bindings,
                value,
                ..
            }) => Ok((*expression, bindings, *value)),
            _ => Err("Evaluation でない".into()),
        }
    }
    fn check_parameter(
        &self,
        graph: &Graph,
        bindings: &[Binding],
        name: &str,
        value: Option<NodeRef>,
    ) -> Result<(), ValidationFailure> {
        let mut binding = None;
        for b in bindings {
            self.tick()?;
            if b.name == name {
                binding = Some(b);
            }
            self.tick()?;
        }
        let b = binding.ok_or("元 parameter 束縛がない")?;
        graph.expect(b.value, &NodeType::Value(b.ty.clone()))?;
        if value != Some(b.value) {
            return Err("parameter の値 Ref 不一致".into());
        }
        Ok(())
    }
    fn check_field(
        &self,
        graph: &Graph,
        base: Option<NodeRef>,
        name: &str,
        value: Option<NodeRef>,
    ) -> Result<(), ValidationFailure> {
        let base = base.ok_or("field の base が未確定")?;
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = graph.scalar(base)?
        else {
            return Err("field の base 型不一致".into());
        };
        let field = self.field(snapshot, subject, &format!("{entity}.{name}"))?;
        match (&field.slot, value) {
            (Slot::Missing, None) => Ok(()),
            (
                Slot::Known {
                    value: expected, ..
                },
                Some(actual),
            ) if scalar_from(expected, &field.ty).as_ref() == Some(graph.scalar(actual)?)
                && graph.get(actual)?.arguments == [base] =>
            {
                Ok(())
            }
            _ => Err("field の元 slot と導出値が合わない".into()),
        }
    }
    fn recheck_evaluation(&self, graph: &Graph, root: NodeRef) -> Result<(), ValidationFailure> {
        let mut pending = vec![root];
        while let Some(reference) = pending.pop() {
            self.tick()?;
            let node = graph.get(reference)?;
            // aggregate の適用検査へ入る前に、子・適用依存が既出であることを確かめる。
            for argument in &node.arguments {
                self.tick()?;
                if argument.0 >= reference.0 {
                    return Err("再検査する評価の引数が既出でない".into());
                }
                self.tick()?;
            }
            self.validate(graph, node)?;
            let Some(Payload::Evaluation {
                expression,
                parts,
                value,
                ..
            }) = &node.payload
            else {
                return Err("再検査対象が Evaluation でない".into());
            };
            self.validate(graph, graph.get(*expression)?)?;
            let mut support = Vec::new();
            if let Some(value) = value {
                self.validate(graph, graph.get(*value)?)?;
                support.extend(graph.get(*value)?.support.iter().cloned());
            }
            for part in parts {
                self.tick()?;
                for &child in &part.children {
                    self.tick()?;
                    if child.0 >= reference.0 {
                        return Err("再検査する子評価が既出でない".into());
                    }
                    pending.push(child);
                    support.extend(graph.get(child)?.support.iter().cloned());
                    self.tick()?;
                }
                self.tick()?;
            }
            support.sort();
            support.dedup();
            if node.support != support {
                return Err("評価の支持が元値・子評価に合わない".into());
            }
            self.tick()?;
        }
        Ok(())
    }
    // LawInstance の適用根拠を元 guard/body と同じ束縛で照合する。
    fn application(
        &self,
        graph: &Graph,
        instance: &Node,
    ) -> Result<(NodeRef, Option<NodeRef>), ValidationFailure> {
        let Some(Payload::LawInstance {
            name,
            body,
            guard,
            bindings,
            ..
        }) = &instance.payload
        else {
            return Err("LawInstance がない".into());
        };
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(name)
            .ok_or("適用の Law 宣言がない")?;
        let crate::law::model::Signature::Law {
            body: source_body,
            guard: source_guard,
            ..
        } = &declaration.signature
        else {
            return Err("適用対象が Law でない".into());
        };
        self.source_matches(graph, *body, *source_body)?;
        match (guard, source_guard) {
            (Some(expression), Some(id)) => self.source_matches(graph, *expression, *id)?,
            (None, None) => {}
            _ => return Err("適用 guard の元宣言不一致".into()),
        }
        let count = 1 + usize::from(guard.is_some());
        if instance.arguments.len() != count + bindings.len() {
            return Err("LawInstance の適用引数数が違う".into());
        }
        let body_evaluation = instance.arguments[0];
        let (expression, body_bindings, _) = self.evaluation(graph, body_evaluation)?;
        if expression != *body
            || body_bindings != bindings
            || self.expression_bindings(graph, expression)? != bindings
        {
            return Err("LawInstance の元 body 評価・束縛不一致".into());
        }
        let guard_evaluation = if let Some(guard) = guard {
            let reference = instance.arguments[1];
            let (expression, guard_bindings, value) = self.evaluation(graph, reference)?;
            if expression != *guard
                || guard_bindings != bindings
                || self.expression_bindings(graph, expression)? != bindings
            {
                return Err("guard 評価の元出現・束縛不一致".into());
            }
            if value.map(|r| graph.scalar(r)).transpose()? != Some(&Scalar::Bool(true)) {
                return Err("guard が確認済み true でない".into());
            }
            self.recheck_evaluation(graph, reference)?;
            Some(reference)
        } else {
            None
        };
        for (binding, &argument) in bindings.iter().zip(&instance.arguments[count..]) {
            self.tick()?;
            if binding.value != argument {
                return Err("適用根拠の parameter identity 不一致".into());
            }
            self.tick()?;
        }
        let (support, scope) =
            self.application_context(graph, body_evaluation, guard_evaluation)?;
        if instance.support != support || instance.scope != scope {
            return Err("LawInstance の適用支持・範囲不一致".into());
        }
        Ok((body_evaluation, guard_evaluation))
    }
    fn application_context(
        &self,
        graph: &Graph,
        body: NodeRef,
        guard: Option<NodeRef>,
    ) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
        let mut support = graph.get(body)?.support.clone();
        let mut scope = graph.get(body)?.scope.clone();
        if let Some(guard) = guard {
            self.tick()?;
            support.extend(graph.get(guard)?.support.iter().cloned());
            scope.merge(&graph.get(guard)?.scope);
            self.tick()?;
        }
        support.sort();
        support.dedup();
        Ok((support, scope))
    }
    fn application_at(
        &self,
        graph: &Graph,
        instance: NodeRef,
    ) -> Result<(NodeRef, Option<NodeRef>), ValidationFailure> {
        let node = graph.get(instance)?;
        for reference in &node.arguments {
            self.tick()?;
            if reference.0 >= instance.0 {
                return Err("LawInstanceの適用引数が既出でない".into());
            }
            self.tick()?;
        }
        self.application(graph, node)
    }
    fn validate_law_evaluation(
        &self,
        graph: &Graph,
        node: &Node,
        instance: NodeRef,
    ) -> Result<(), ValidationFailure> {
        let (body, guard) = self.application_at(graph, instance)?;
        let guard = guard.ok_or("省略 guard に適用集約評価を作っている")?;
        if node.arguments != [instance, body, guard] {
            return Err("適用評価の元引数不一致".into());
        }
        let Some(Payload::Evaluation {
            expression,
            bindings,
            parts,
            value,
            applicability,
        }) = &node.payload
        else {
            return Err("適用評価でない".into());
        };
        let (body_expression, body_bindings, body_value) = self.evaluation(graph, body)?;
        if *expression != body_expression
            || bindings != body_bindings
            || *value != body_value
            || *applicability != "applicable"
            || parts.len() != 2
        {
            return Err("適用評価の元 body・束縛・適用表示不一致".into());
        }
        for (part, evaluation) in parts.iter().zip([guard, body]) {
            self.tick()?;
            let (expression, _, value) = self.evaluation(graph, evaluation)?;
            let Some(Payload::Evaluation {
                parts: original, ..
            }) = &graph.get(evaluation)?.payload
            else {
                unreachable!()
            };
            if part.location
                != (Location::Law {
                    span: self.expression_span(graph, expression)?,
                })
                || part.value != value
                || part.residual != original.last().ok_or("元評価 part がない")?.residual
                || part.children != [evaluation]
            {
                return Err("適用評価 part の出現・値・子評価不一致".into());
            }
            self.tick()?;
        }
        let (support, scope) = self.application_context(graph, body, Some(guard))?;
        if node.support != support || node.scope != scope {
            return Err("適用評価の支持・範囲不一致".into());
        }
        Ok(())
    }
    fn instance_evaluation(
        &self,
        graph: &Graph,
        instance: NodeRef,
        evaluation: NodeRef,
    ) -> Result<NodeRef, ValidationFailure> {
        let (body, guard) = self.application_at(graph, instance)?;
        if guard.is_some() {
            self.validate_law_evaluation(graph, graph.get(evaluation)?, instance)?;
        } else if evaluation != body {
            return Err("省略 guard の元 body 評価不一致".into());
        }
        Ok(body)
    }
    fn evidence_operands(
        &self,
        graph: &Graph,
        node: &Node,
        instance: NodeRef,
    ) -> Result<(NodeRef, NodeRef, NodeRef), ValidationFailure> {
        if node.arguments.len() != 2 || node.arguments[0] != instance {
            return Err("証拠の構成入力不一致".into());
        }
        let evaluation = node.arguments[1];
        let body = self.instance_evaluation(graph, instance, evaluation)?;
        let (expression, _, value) = self.evaluation(graph, body)?;
        let span = self.expression_span(graph, expression)?;
        let expr =
            &self.inputs.law().exprs[*self.expressions.get(&span).ok_or("証拠の元 AST がない")?];
        if matches!(expr.kind, ExprKind::Binary { .. }) {
            let Some(Payload::Evaluation { parts, .. }) = &graph.get(body)?.payload else {
                unreachable!()
            };
            if parts[0].children.len() != 2 {
                return Err("比較証拠の子評価数".into());
            }
            let (_, _, left) = self.evaluation(graph, parts[0].children[0])?;
            let (_, _, right) = self.evaluation(graph, parts[0].children[1])?;
            Ok((
                evaluation,
                left.ok_or("左辺が未確定")?,
                right.ok_or("右辺が未確定")?,
            ))
        } else {
            let left = value.ok_or("Bool body が未確定")?;
            let supplied_right = match &node.payload {
                Some(Payload::Counterexample { right, .. }) => *right,
                Some(Payload::EvaluationEvidence { rhs, .. }) => *rhs,
                _ => return Err("証拠 payload の種類".into()),
            };
            if graph.scalar(supplied_right)? != &Scalar::Bool(true)
                || graph.get(supplied_right)?.arguments != [instance]
            {
                return Err("Bool 証拠の true 要求が違う".into());
            }
            let Some(Payload::LawInstance {
                body,
                guard,
                bindings,
                ..
            }) = &graph.get(instance)?.payload
            else {
                return Err("固定trueの元LawInstanceがない".into());
            };
            let mut expected =
                self.source_scope(graph, self.expression_span(graph, *body)?, bindings)?;
            if let Some(guard) = guard {
                self.tick()?;
                expected.merge(&self.source_scope(
                    graph,
                    self.expression_span(graph, *guard)?,
                    bindings,
                )?);
                self.tick()?;
            }
            if graph.get(supplied_right)?.scope != expected {
                return Err("固定true Scalarの範囲が元Law適用と違う".into());
            }
            Ok((evaluation, left, supplied_right))
        }
    }
    fn source_matches(&self, graph: &Graph, r: NodeRef, id: usize) -> Result<(), String> {
        match &graph.get(r)?.payload {
            Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) if *span == self.inputs.law().exprs[id].span => Ok(()),
            _ => Err("元式との出現不一致".into()),
        }
    }
}
pub(crate) fn scalar_from(value: &Value, ty: &Type) -> Option<Scalar> {
    match value {
        Value::Z(n) => Some(Scalar::Z(n.clone())),
        Value::Bool(b) => Some(Scalar::Bool(*b)),
        Value::Ref { snapshot, subject } => Some(Scalar::Subject {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            entity: ty.ref_target()?.into(),
        }),
        _ => None,
    }
}
pub(crate) fn binary(op: BinOp, left: &Scalar, right: &Scalar) -> Result<Scalar, String> {
    let result = match (left, right) {
        (Scalar::Z(a), Scalar::Z(b)) => match op {
            BinOp::Eq => a == b,
            BinOp::Ne => a != b,
            BinOp::Lt => a < b,
            BinOp::Le => a <= b,
            BinOp::Gt => a > b,
            BinOp::Ge => a >= b,
            _ => return Err("未実装の整数演算".into()),
        },
        (Scalar::Bool(a), Scalar::Bool(b)) => match op {
            BinOp::Eq => a == b,
            BinOp::Ne => a != b,
            _ => return Err("未実装の Bool 演算".into()),
        },
        _ => return Err("比較値の型が合わない".into()),
    };
    Ok(Scalar::Bool(result))
}
