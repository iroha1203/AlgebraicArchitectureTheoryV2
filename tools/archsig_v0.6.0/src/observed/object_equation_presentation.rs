//! 選択対象の元Law導出から、原始slotを共有する型別K[X]とrequired idealを作る。
use super::{
    control::{Checkpoint, Control},
    equation_polynomial::{EquationPolynomial, invalid, tick},
    input::CheckedInputs,
    numeric,
    numeric_transport::NumericTransportValue,
    object_evaluate::ObjectEvaluationOutcome,
    object_law_residuals::{
        LawNumericShape, LawResidualCase, ObjectLawResiduals, ObjectLawResidualsFailure,
        object_law_residuals,
    },
    object_law_transport::LawApplication,
    result::{Fact, NodeRef, ObservedEvaluation, Payload, Scalar},
};
use crate::{
    construction::{ConstructionFailure, readings::ObjectEvaluationPosition},
    issue::Location,
    law::ast::{BinOp, ExprKind, UnOp},
    types::Type,
};
use std::sync::Arc;
#[path = "equation_source_polynomial.rs"]
mod source_polynomial;
fn bad(s: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(s.into())
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquationSlot {
    pub snapshot: String,
    pub subject: String,
    pub field: String,
    pub component: Vec<usize>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquationSymbolReading {
    pub position: ObjectEvaluationPosition,
    pub row: Option<usize>,
    pub case: usize,
    pub evaluation: usize,
    pub value: Option<usize>,
    pub location: Location,
    /// 元caseでの代入。未観測slotの補完caseを観測事実とは区別する。
    pub assignment: Option<NumericTransportValue>,
    /// slot identityとは別の、既知Atomとその由来へ戻る元支持。
    pub fact: Fact,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquationSymbol {
    pub slot: EquationSlot,
    pub value: Option<NumericTransportValue>,
    pub readings: Vec<EquationSymbolReading>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquationRing {
    pub ty: Type,
    pub symbols: Vec<EquationSymbol>,
    /// 各記号のKへの像を定数多項式で保持する。欠測時は全域evAを作らない。
    pub evaluation_images: Option<Vec<EquationPolynomial>>,
    /// occurrences()の添字。対応νが、この同じK[X]のideal生成元。
    pub required_generators: Vec<usize>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquationStep {
    pub evaluation: usize,
    pub location: Location,
    pub component: Vec<usize>,
    pub polynomial: EquationPolynomial,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EquationGuard {
    AlwaysTrue,
    AlwaysFalse,
    OutsideObject,
    StateDependent,
    Undetermined,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EquationPresentationStatus {
    Ready,
    NotApplicable,
    Undetermined,
    UnsupportedAlgorithm,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquationOccurrence {
    pub position: ObjectEvaluationPosition,
    pub row: Option<usize>,
    pub case: usize,
    pub component: Vec<usize>,
    pub ty: Type,
    pub required: bool,
    pub guard: EquationGuard,
    pub evaluation: Option<usize>,
    pub operands: Vec<usize>,
    pub epsilon_producer: Option<usize>,
    pub ring: Option<usize>,
    pub left: Option<EquationPolynomial>,
    pub right: Option<EquationPolynomial>,
    pub nu: Option<EquationPolynomial>,
    /// 元Evaluatorの生差と適用条件付き残差。idealで割らない。
    pub epsilon: Option<NumericTransportValue>,
    pub residual: Option<NumericTransportValue>,
    pub evaluated_nu: Option<NumericTransportValue>,
    pub epsilon_constant: Option<EquationPolynomial>,
    pub residual_constant: Option<EquationPolynomial>,
    pub component_holds: Option<bool>,
    pub steps: Vec<EquationStep>,
    pub status: EquationPresentationStatus,
}
#[derive(Debug)]
pub struct EquationPresentation {
    base: ObjectLawResiduals,
    object: usize,
    rings: Vec<EquationRing>,
    occurrences: Vec<EquationOccurrence>,
    complete: bool,
}
impl EquationPresentation {
    pub fn base(&self) -> &ObjectLawResiduals {
        &self.base
    }
    pub fn object(&self) -> usize {
        self.object
    }
    pub fn rings(&self) -> &[EquationRing] {
        &self.rings
    }
    pub fn occurrences(&self) -> &[EquationOccurrence] {
        &self.occurrences
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    pub fn status(&self) -> EquationPresentationStatus {
        if self
            .occurrences
            .iter()
            .any(|q| q.status == EquationPresentationStatus::UnsupportedAlgorithm)
        {
            EquationPresentationStatus::UnsupportedAlgorithm
        } else if !self.complete
            || self
                .occurrences
                .iter()
                .any(|q| q.status == EquationPresentationStatus::Undetermined)
        {
            EquationPresentationStatus::Undetermined
        } else {
            EquationPresentationStatus::Ready
        }
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<(), EquationPresentationFailure> {
        self.base
            .recheck(Arc::clone(&inputs), c)
            .map_err(EquationPresentationFailure::Original)?;
        let root = self.base.base().readings().construction().root();
        let expected = object_equation_presentation(
            inputs,
            self.base.base().readings().construction().reading(),
            &root.snapshot,
            &root.subject,
            self.object,
            c,
        )?;
        let checked = (|| -> Result<bool, ConstructionFailure> {
            tick(c)?;
            if self.object != expected.object
                || self.complete != expected.complete
                || self.rings.len() != expected.rings.len()
                || self.occurrences.len() != expected.occurrences.len()
            {
                return Ok(false);
            }
            for (a, b) in self.rings.iter().zip(&expected.rings) {
                tick(c)?;
                if a != b {
                    return Ok(false);
                }
            }
            for (a, b) in self.occurrences.iter().zip(&expected.occurrences) {
                tick(c)?;
                if a != b {
                    return Ok(false);
                }
            }
            tick(c)?;
            Ok(true)
        })();
        match checked {
            Ok(true) => Ok(()),
            other => Err(EquationPresentationFailure::Reading {
                cause: other
                    .err()
                    .unwrap_or_else(|| bad("共有方程式表示が現在三入力の元導出と違う")),
                partial: Box::new(expected),
            }),
        }
    }
}
#[derive(Debug)]
pub enum EquationPresentationFailure {
    Original(ObjectLawResidualsFailure),
    Selection(ConstructionFailure),
    Reading {
        cause: ConstructionFailure,
        partial: Box<EquationPresentation>,
    },
}
impl EquationPresentationFailure {
    pub fn partial(&self) -> Option<&EquationPresentation> {
        match self {
            Self::Reading { partial, .. } => Some(partial),
            _ => None,
        }
    }
}
fn part(g: &ObservedEvaluation, r: NodeRef) -> Result<&super::result::Part, ConstructionFailure> {
    match g.nodes.get(r.0).and_then(|n| n.payload.as_ref()) {
        Some(Payload::Evaluation { parts, .. }) if parts.len() == 1 => Ok(&parts[0]),
        _ => Err(bad("多項式の元評価が単一の原式出現でない")),
    }
}
fn scalar(g: &ObservedEvaluation, r: NodeRef) -> Option<&Scalar> {
    match g.nodes.get(r.0)?.payload.as_ref()? {
        Payload::Scalar(s) => Some(s),
        _ => None,
    }
}
fn projected(s: &Scalar, path: &[usize]) -> Option<Scalar> {
    let mut s = s;
    for &i in path {
        let Scalar::Tuple(items) = s else { return None };
        s = items.get(i)?;
    }
    Some(s.clone())
}
fn value(g: &ObservedEvaluation, r: NodeRef, path: &[usize]) -> Option<Scalar> {
    projected(scalar(g, part(g, r).ok()?.value?)?, path)
}
fn has_fields(
    g: &ObservedEvaluation,
    r: NodeRef,
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    let n = g
        .nodes
        .get(r.0)
        .ok_or_else(|| bad("原始依存の元評価がない"))?;
    for fact in n
        .support
        .iter()
        .chain(n.reasons.iter().flat_map(|reason| &reason.missing))
    {
        tick(c)?;
        if fact.field.is_some() {
            return Ok(true);
        }
    }
    Ok(false)
}
fn ring(
    rings: &mut Vec<EquationRing>,
    ty: &Type,
    c: &mut Control,
) -> Result<usize, ConstructionFailure> {
    for (i, r) in rings.iter().enumerate() {
        tick(c)?;
        if &r.ty == ty {
            return Ok(i);
        }
    }
    rings.push(EquationRing {
        ty: ty.clone(),
        symbols: vec![],
        evaluation_images: Some(vec![]),
        required_generators: vec![],
    });
    Ok(rings.len() - 1)
}
struct Compiler<'a> {
    inputs: &'a CheckedInputs,
    g: &'a ObservedEvaluation,
    ring: &'a mut EquationRing,
    position: ObjectEvaluationPosition,
    row: Option<usize>,
    case: usize,
    steps: Vec<EquationStep>,
}
impl Compiler<'_> {
    fn field(
        &mut self,
        r: NodeRef,
        name: &str,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<EquationPolynomial>, ConstructionFailure> {
        let p = part(self.g, r)?;
        let Some(&base) = p.children.first() else {
            return Ok(None);
        };
        let reference = value(self.g, base, &[]);
        let Some(Scalar::Subject {
            snapshot,
            subject,
            entity,
        }) = reference.as_ref()
        else {
            return Ok(None);
        };
        let field = format!("{entity}.{name}");
        let n = &self.g.nodes[r.0];
        let fact = n
            .support
            .iter()
            .chain(n.reasons.iter().flat_map(|r| &r.missing))
            .find(|f| {
                f.snapshot == *snapshot && f.subject == *subject && f.field.as_ref() == Some(&field)
            })
            .cloned();
        let Some(fact) = fact else { return Ok(None) };
        let assignment = value(self.g, r, path).map(NumericTransportValue::observed);
        let observed = fact.atom.as_ref().and(assignment.clone());
        if observed.as_ref().is_some_and(|v| v.ty() != self.ring.ty) {
            return Err(bad("原始記号の数値成分型が違う"));
        }
        let slot = EquationSlot {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field,
            component: path.to_vec(),
        };
        let mut index = None;
        for (i, s) in self.ring.symbols.iter().enumerate() {
            tick(c)?;
            if s.slot == slot {
                index = Some(i);
                break;
            }
        }
        let i = if let Some(i) = index {
            if self.ring.symbols[i].value != observed {
                return Err(bad("同じ原始slotに異なる代入がある"));
            }
            i
        } else {
            if let Some(observed) = &observed {
                if let Some(images) = &mut self.ring.evaluation_images {
                    images.push(EquationPolynomial::constant(observed.scalar().clone(), c)?);
                }
            } else {
                self.ring.evaluation_images = None;
            }
            self.ring.symbols.push(EquationSymbol {
                slot,
                value: observed,
                readings: vec![],
            });
            self.ring.symbols.len() - 1
        };
        let reading = EquationSymbolReading {
            position: self.position,
            row: self.row,
            case: self.case,
            evaluation: r.0,
            value: p.value.map(|v| v.0),
            location: p.location.clone(),
            assignment,
            fact,
        };
        if !self.ring.symbols[i].readings.contains(&reading) {
            self.ring.symbols[i].readings.push(reading);
        }
        Ok(Some(EquationPolynomial::variable(&self.ring.ty, i, c)?))
    }
    fn is_helper(&self, mut callee: usize, c: &mut Control) -> Result<bool, ConstructionFailure> {
        while let ExprKind::Group(child) = self.inputs.law().exprs[callee].kind {
            tick(c)?;
            callee = child;
        }
        let span = self.inputs.law().exprs[callee].span;
        for info in &self.inputs.law().infos {
            for (at, target) in &info.references {
                tick(c)?;
                if *at == span
                    && self.inputs.law().declarations.get(target).is_some_and(|d| {
                        matches!(d.signature, crate::law::model::Signature::View { .. })
                    })
                {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }
    // 元の実読取りはfieldで保持し、νに使うときだけ位置の固定性を要求する。
    fn polynomial_field(
        &mut self,
        r: NodeRef,
        name: &str,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<EquationPolynomial>, ConstructionFailure> {
        let Some(&base) = part(self.g, r)?.children.first() else {
            return Ok(None);
        };
        if !self.fixed_reference(base, &[], c)? {
            return Ok(None);
        }
        self.field(r, name, path, c)
    }
    fn fixed_field_reference(
        &self,
        r: NodeRef,
        name: &str,
        c: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        let p = part(self.g, r)?;
        let [base] = p.children.as_slice() else {
            return Ok(false);
        };
        let reference = value(self.g, *base, &[]);
        let Some(Scalar::Subject {
            snapshot,
            subject,
            entity,
        }) = reference.as_ref()
        else {
            return Ok(false);
        };
        let field = format!("{entity}.{name}");
        // 補完caseのSubject値は観測済みの参照Atomではない。
        let mut observed = false;
        for fact in &self.g.nodes[r.0].support {
            tick(c)?;
            if fact.snapshot == *snapshot
                && fact.subject == *subject
                && fact.field.as_ref() == Some(&field)
            {
                observed |= fact.atom.is_some();
            }
        }
        Ok(observed && self.fixed_reference(*base, &[], c)?)
    }
    fn fixed_match(
        &self,
        r: NodeRef,
        scrutinee: usize,
        arms: &[crate::law::ast::Arm],
        c: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        let p = part(self.g, r)?;
        if p.children.len() != 2 {
            return Ok(false);
        }
        if !has_fields(self.g, p.children[0], c)? {
            return Ok(true);
        }
        Ok(
            super::object_law_residuals::binding_match_body(self.inputs, scrutinee, arms, c)?
                .is_some(),
        )
    }
    // Refの実値だけでなく、その選択導出が数値記号に依存しないことを確認する。
    fn fixed_reference(
        &self,
        r: NodeRef,
        path: &[usize],
        c: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            tick(c)?;
            if !matches!(value(self.g, r, path), Some(Scalar::Subject { .. })) {
                return Ok(false);
            }
            let p = part(self.g, r)?;
            let Location::Law { span } = p.location else {
                return Ok(false);
            };
            // dottedの中間prefixも元token位置を用いる。架空のASTを作らない。
            for expression in &self.inputs.law().exprs {
                tick(c)?;
                if let ExprKind::Dotted(names) = &expression.kind {
                    if names.first().is_some_and(|n| n.span.0 == span.0) {
                        if let Some(index) = names.iter().position(|n| n.span.1 == span.1) {
                            return if index == 0 {
                                match p.children.as_slice() {
                                    [child] => self.fixed_reference(*child, path, c),
                                    [] => Ok(!has_fields(self.g, r, c)?),
                                    _ => Ok(false),
                                }
                            } else {
                                self.fixed_field_reference(r, &names[index].name, c)
                            };
                        }
                    }
                }
                if expression.span != span {
                    continue;
                }
                return match &expression.kind {
                    ExprKind::Group(_) if p.children.len() == 1 => {
                        self.fixed_reference(p.children[0], path, c)
                    }
                    ExprKind::Let { .. } if p.children.len() == 2 => {
                        self.fixed_reference(p.children[1], path, c)
                    }
                    ExprKind::Field { name, .. } if p.children.len() == 1 => {
                        self.fixed_field_reference(r, &name.name, c)
                    }
                    ExprKind::Tuple(_) if !path.is_empty() => match p.children.get(path[0]) {
                        Some(&child) => self.fixed_reference(child, &path[1..], c),
                        None => Ok(false),
                    },
                    ExprKind::Index { index, .. } if p.children.len() == 1 => {
                        let mut nested = vec![*index];
                        nested.extend_from_slice(path);
                        self.fixed_reference(p.children[0], &nested, c)
                    }
                    ExprKind::If { .. } if p.children.len() == 3 => {
                        if !has_fields(self.g, p.children[0], c)? {
                            match value(self.g, p.children[0], &[]) {
                                Some(Scalar::Bool(b)) => {
                                    self.fixed_reference(p.children[if b { 1 } else { 2 }], path, c)
                                }
                                _ => Ok(false),
                            }
                        } else {
                            // 両枝が同じ固定参照なら、条件の値によらず同じ位置を読む。
                            Ok(self.fixed_reference(p.children[1], path, c)?
                                && self.fixed_reference(p.children[2], path, c)?
                                && value(self.g, p.children[1], path)
                                    == value(self.g, p.children[2], path))
                        }
                    }
                    ExprKind::Call { callee, args }
                        if p.children.len() == args.len() + 1 && self.is_helper(*callee, c)? =>
                    {
                        self.fixed_reference(p.children[p.children.len() - 1], path, c)
                    }
                    ExprKind::Match { scrutinee, arms }
                        if self.fixed_match(r, *scrutinee, arms, c)? =>
                    {
                        self.fixed_reference(p.children[1], path, c)
                    }
                    _ => Ok(false),
                };
            }
            Ok(false)
        })
    }
    // 元導出の論理則と同じ共有slotの多項式正規化で、全域確定だけを証明する。
    // 観測したBoolを状態全域の値へ昇格させず、証明できない場合はNoneを返す。
    fn constant_boolean(
        &mut self,
        r: NodeRef,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<bool>, ConstructionFailure> {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            tick(c)?;
            if !has_fields(self.g, r, c)? {
                return Ok(match value(self.g, r, path) {
                    Some(Scalar::Bool(b)) => Some(b),
                    _ => None,
                });
            }
            let p = part(self.g, r)?.clone();
            let Location::Law { span } = p.location else {
                return Ok(None);
            };
            let mut expression = None;
            for e in &self.inputs.law().exprs {
                tick(c)?;
                if e.span == span {
                    expression = Some(e);
                    break;
                }
            }
            let Some(expression) = expression else {
                return Ok(None);
            };
            match &expression.kind {
                ExprKind::Group(_) | ExprKind::Dotted(_) if p.children.len() == 1 => {
                    // fieldの子は参照でありBoolではないので、原始Bool値を定数化しない。
                    self.constant_boolean(p.children[0], path, c)
                }
                ExprKind::Let { .. } if p.children.len() == 2 => {
                    self.constant_boolean(p.children[1], path, c)
                }
                ExprKind::Tuple(_) if !path.is_empty() => match p.children.get(path[0]) {
                    Some(&child) => self.constant_boolean(child, &path[1..], c),
                    None => Ok(None),
                },
                ExprKind::Index { index, .. } if p.children.len() == 1 => {
                    let mut nested = vec![*index];
                    nested.extend_from_slice(path);
                    self.constant_boolean(p.children[0], &nested, c)
                }
                ExprKind::Unary { op: UnOp::Not, .. }
                    if p.children.len() == 1 && path.is_empty() =>
                {
                    Ok(self.constant_boolean(p.children[0], &[], c)?.map(|b| !b))
                }
                ExprKind::Binary { op, .. } if p.children.len() == 2 && path.is_empty() => {
                    let [left, right] = [p.children[0], p.children[1]];
                    if matches!(op, BinOp::And | BinOp::Or | BinOp::Implies) {
                        let a = self.constant_boolean(left, &[], c)?;
                        let b = self.constant_boolean(right, &[], c)?;
                        return Ok(match (op, a, b) {
                            (BinOp::And, Some(false), _) | (BinOp::And, _, Some(false)) => {
                                Some(false)
                            }
                            (BinOp::And, Some(true), Some(true)) => Some(true),
                            (BinOp::Or, Some(true), _) | (BinOp::Or, _, Some(true)) => Some(true),
                            (BinOp::Or, Some(false), Some(false)) => Some(false),
                            (BinOp::Implies, Some(false), _) | (BinOp::Implies, _, Some(true)) => {
                                Some(true)
                            }
                            (BinOp::Implies, Some(true), Some(false)) => Some(false),
                            _ => None,
                        });
                    }
                    if matches!(
                        op,
                        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                    ) {
                        let super::result::NodeType::Evaluation(ty) = &self.g.nodes[left.0].ty
                        else {
                            return Ok(None);
                        };
                        if *ty == Type::Bool && matches!(op, BinOp::Eq | BinOp::Ne) {
                            return Ok(self
                                .constant_boolean(left, &[], c)?
                                .zip(self.constant_boolean(right, &[], c)?)
                                .map(|(a, b)| if *op == BinOp::Eq { a == b } else { a != b }));
                        }
                        return self.constant_comparison(*op, left, right, ty, &[], c);
                    }
                    Ok(None)
                }
                ExprKind::If { .. } if p.children.len() == 3 => {
                    match self.constant_boolean(p.children[0], &[], c)? {
                        Some(b) => {
                            self.constant_boolean(p.children[if b { 1 } else { 2 }], path, c)
                        }
                        None => {
                            let a = self.constant_boolean(p.children[1], path, c)?;
                            let b = self.constant_boolean(p.children[2], path, c)?;
                            Ok(a.filter(|_| a == b))
                        }
                    }
                }
                ExprKind::Call { callee, args }
                    if p.children.len() == args.len() + 1 && self.is_helper(*callee, c)? =>
                {
                    self.constant_boolean(p.children[p.children.len() - 1], path, c)
                }
                ExprKind::Match { scrutinee, arms }
                    if self.fixed_match(r, *scrutinee, arms, c)? =>
                {
                    self.constant_boolean(p.children[1], path, c)
                }
                _ => Ok(None),
            }
        })
    }
    fn constant_comparison(
        &self,
        op: BinOp,
        left: NodeRef,
        right: NodeRef,
        ty: &Type,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<bool>, ConstructionFailure> {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            tick(c)?;
            if let Type::Tuple(items) = ty {
                if !matches!(op, BinOp::Eq | BinOp::Ne) {
                    return Ok(None);
                }
                let mut equal = Some(true);
                for (i, item) in items.iter().enumerate() {
                    let mut component = path.to_vec();
                    component.push(i);
                    match self.constant_comparison(BinOp::Eq, left, right, item, &component, c)? {
                        Some(false) => return Ok(Some(op == BinOp::Ne)),
                        None => equal = None,
                        _ => (),
                    }
                }
                return Ok(equal.map(|b| if op == BinOp::Eq { b } else { !b }));
            }
            if !matches!(ty, Type::Z | Type::Q | Type::Fp(_)) {
                return Ok(None);
            }
            let mut ring = EquationRing {
                ty: ty.clone(),
                symbols: vec![],
                evaluation_images: Some(vec![]),
                required_generators: vec![],
            };
            let mut compiler = Compiler {
                inputs: self.inputs,
                g: self.g,
                ring: &mut ring,
                position: self.position,
                row: self.row,
                case: self.case,
                steps: vec![],
            };
            let a = compiler.compile(left, path, c)?;
            let b = compiler.compile(right, path, c)?;
            let Some((a, b)) = a.zip(b) else {
                return Ok(None);
            };
            let difference = a.binary(BinOp::Sub, &b, c)?;
            if difference.terms.iter().any(|t| !t.variables.is_empty()) {
                return Ok(None);
            }
            let zero = numeric::zero(ty, c).map_err(invalid)?;
            let constant = difference
                .terms
                .first()
                .map(|t| t.coefficient.scalar())
                .unwrap_or(&zero);
            match numeric::binary(op, constant, &zero, c).map_err(invalid)? {
                Scalar::Bool(b) => Ok(Some(b)),
                _ => Err(bad("guard比較の戻り値がBoolでない")),
            }
        })
    }
    // 値の正規化で不要になるlet/helper引数/Tuple位置も、元読取りとして収集する。
    fn collect_support(
        &mut self,
        root: NodeRef,
        c: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        let mut pending = vec![root];
        let mut seen = std::collections::BTreeSet::new();
        while let Some(r) = pending.pop() {
            tick(c)?;
            if !seen.insert(r.0) {
                continue;
            }
            let n = self
                .g
                .nodes
                .get(r.0)
                .ok_or_else(|| bad("支持収集の元nodeがない"))?;
            let Some(Payload::Evaluation { parts, .. }) = &n.payload else {
                return Err(bad("支持収集の元nodeが評価でない"));
            };
            for p in parts.iter().rev() {
                for &child in p.children.iter().rev() {
                    tick(c)?;
                    if child.0 >= r.0 {
                        return Err(bad("支持収集が元導出順でない"));
                    }
                    pending.push(child);
                }
            }
            if parts.len() != 1 {
                continue;
            }
            let Location::Law { span } = parts[0].location else {
                continue;
            };
            let mut field = None;
            for e in &self.inputs.law().exprs {
                tick(c)?;
                if e.span == span {
                    field = match &e.kind {
                        ExprKind::Field { name, .. } => Some(name.name.clone()),
                        ExprKind::Dotted(names) if names.len() > 1 => {
                            Some(names[names.len() - 1].name.clone())
                        }
                        _ => None,
                    };
                    break;
                }
            }
            let Some(name) = field else { continue };
            let super::result::NodeType::Evaluation(ty) = &n.ty else {
                return Err(bad("支持収集の元型がない"));
            };
            let mut paths = vec![];
            let mut stack = vec![(ty, vec![])];
            while let Some((ty, path)) = stack.pop() {
                tick(c)?;
                if ty == &self.ring.ty {
                    paths.push(path);
                } else if let Type::Tuple(items) = ty {
                    for (i, ty) in items.iter().enumerate().rev() {
                        tick(c)?;
                        let mut path = path.clone();
                        path.push(i);
                        stack.push((ty, path));
                    }
                }
            }
            for path in paths {
                self.field(r, &name, &path, c)?;
            }
        }
        Ok(())
    }
    fn compile(
        &mut self,
        r: NodeRef,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<EquationPolynomial>, ConstructionFailure> {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            tick(c)?;
            let p = part(self.g, r)?.clone();
            if p.children.iter().any(|child| child.0 >= r.0) {
                return Err(bad("多項式の元評価が導出順でない"));
            }
            let Location::Law { span } = p.location else {
                return Ok(None);
            };
            let mut expression = None;
            for e in &self.inputs.law().exprs {
                tick(c)?;
                if e.span == span {
                    expression = Some(e);
                    break;
                }
            }
            let Some(expression) = expression else {
                return Ok(None);
            };
            let out = match &expression.kind {
                ExprKind::Int(_) => value(self.g, r, path)
                    .map(|s| EquationPolynomial::constant(s, c))
                    .transpose()?,
                ExprKind::Group(_) if p.children.len() == 1 => {
                    self.compile(p.children[0], path, c)?
                }
                ExprKind::Tuple(_) if !path.is_empty() => match p.children.get(path[0]) {
                    Some(&child) => self.compile(child, &path[1..], c)?,
                    None => None,
                },
                ExprKind::Index { index, .. } if p.children.len() == 1 => {
                    let mut nested = vec![*index];
                    nested.extend_from_slice(path);
                    self.compile(p.children[0], &nested, c)?
                }
                ExprKind::Unary { op: UnOp::Neg, .. } if p.children.len() == 1 => match self
                    .compile(p.children[0], path, c)?
                {
                    Some(v) => Some(
                        EquationPolynomial::constant(numeric::zero(&v.ty, c).map_err(invalid)?, c)?
                            .binary(BinOp::Sub, &v, c)?,
                    ),
                    None => None,
                },
                ExprKind::Binary { op, .. }
                    if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul)
                        && p.children.len() == 2 =>
                {
                    let a = self.compile(p.children[0], path, c)?;
                    let b = self.compile(p.children[1], path, c)?;
                    match (a, b) {
                        (Some(a), Some(b)) => Some(a.binary(*op, &b, c)?),
                        _ => None,
                    }
                }
                ExprKind::Field { name, .. } => self.polynomial_field(r, &name.name, path, c)?,
                ExprKind::Dotted(names) if names.len() > 1 => {
                    self.polynomial_field(r, &names[names.len() - 1].name, path, c)?
                }
                ExprKind::Dotted(_) if p.children.len() == 1 => {
                    self.compile(p.children[0], path, c)?
                }
                ExprKind::Dotted(_) if p.children.is_empty() && !has_fields(self.g, r, c)? => {
                    // 元の有限型parameter代入。無限域の標本へは使わない。
                    value(self.g, r, path)
                        .map(|s| EquationPolynomial::constant(s, c))
                        .transpose()?
                }
                ExprKind::Let { .. } if p.children.len() == 2 => {
                    self.compile(p.children[1], path, c)?
                }
                ExprKind::Match { scrutinee, arms }
                    if self.fixed_match(r, *scrutinee, arms, c)? =>
                {
                    self.compile(p.children[1], path, c)?
                }
                ExprKind::If { .. }
                    if p.children.len() == 3 && !has_fields(self.g, p.children[0], c)? =>
                {
                    match value(self.g, p.children[0], &[]) {
                        Some(Scalar::Bool(b)) => {
                            self.compile(p.children[if b { 1 } else { 2 }], path, c)?
                        }
                        _ => None,
                    }
                }
                ExprKind::Call { callee, args }
                    if p.children.len() == args.len() + 1 && self.is_helper(*callee, c)? =>
                {
                    self.compile(
                        *p.children.last().ok_or_else(|| bad("helper bodyがない"))?,
                        path,
                        c,
                    )?
                }
                // rat等の純粋定数構成。fieldに依存する変換を定数へ落とさない。
                ExprKind::Call { .. } if !has_fields(self.g, r, c)? => value(self.g, r, path)
                    .map(|s| EquationPolynomial::constant(s, c))
                    .transpose()?,
                _ => None,
            };
            if let Some(polynomial) = &out {
                if polynomial.ty != self.ring.ty {
                    return Err(bad("元多項式の成分型が係数環と違う"));
                }
                self.steps.push(EquationStep {
                    evaluation: r.0,
                    location: p.location,
                    component: path.to_vec(),
                    polynomial: polynomial.clone(),
                });
            }
            tick(c)?;
            Ok(out)
        })
    }
}
fn guard(
    inputs: &CheckedInputs,
    position: ObjectEvaluationPosition,
    row: Option<usize>,
    case_index: usize,
    g: Option<&ObservedEvaluation>,
    case: &LawResidualCase,
    explicit: bool,
    c: &mut Control,
) -> Result<EquationGuard, ConstructionFailure> {
    tick(c)?;
    match case.reading.application() {
        LawApplication::OutsideObject => return Ok(EquationGuard::OutsideObject),
        LawApplication::ConditionalMembership(_) => return Ok(EquationGuard::Undetermined),
        _ => (),
    }
    if !explicit {
        return Ok(EquationGuard::AlwaysTrue);
    }
    let Some((g, reference)) = g.zip(case.evaluation) else {
        return Ok(EquationGuard::Undetermined);
    };
    let Some(Payload::Evaluation { parts, .. }) =
        g.nodes.get(reference).and_then(|n| n.payload.as_ref())
    else {
        return Err(bad("元guard評価がない"));
    };
    let Some(&child) = parts.first().and_then(|p| p.children.first()) else {
        return Err(bad("元guard子がない"));
    };
    let mut ring = EquationRing {
        ty: Type::Z,
        symbols: vec![],
        evaluation_images: Some(vec![]),
        required_generators: vec![],
    };
    let mut compiler = Compiler {
        inputs,
        g,
        ring: &mut ring,
        position,
        row,
        case: case_index,
        steps: vec![],
    };
    if let Some(b) = compiler.constant_boolean(child, &[], c)? {
        return Ok(if b {
            EquationGuard::AlwaysTrue
        } else {
            EquationGuard::AlwaysFalse
        });
    }
    if case.reading.application().value().is_none() {
        return Ok(EquationGuard::Undetermined);
    }
    if has_fields(g, child, c)? {
        return Ok(EquationGuard::StateDependent);
    }
    Ok(match case.reading.application().value() {
        Some(true) => EquationGuard::AlwaysTrue,
        Some(false) => EquationGuard::AlwaysFalse,
        None => EquationGuard::Undetermined,
    })
}
fn populate(
    r: &mut EquationPresentation,
    inputs: &CheckedInputs,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    // work列は元行への添字のみ。出現/係数を事前に供給しない。
    let mut work = vec![];
    let mut families_complete = true;
    for (i, e) in r.base.evaluations().iter().enumerate() {
        tick(c)?;
        if e.position.object != r.object {
            continue;
        }
        // 未確定のparameter域は、出現行が零でも完成した空族ではない。
        families_complete &= e.complete;
        for (row, v) in e.rows.iter().enumerate() {
            for (case, _) in v.cases.iter().enumerate() {
                tick(c)?;
                work.push((i, Some(row), case));
            }
        }
        if let Some(v) = &e.uniform {
            for (case, _) in v.cases.iter().enumerate() {
                tick(c)?;
                work.push((i, None, case));
            }
        }
    }
    let mut count = 0;
    for &(i, row, case) in &work {
        let e = &r.base.evaluations()[i];
        let q = match row {
            Some(row) => &e.rows[row].cases[case],
            None => {
                &e.uniform
                    .as_ref()
                    .ok_or_else(|| bad("uniform行がない"))?
                    .cases[case]
            }
        };
        count += q.components.len().max(1);
    }
    for (i, row, case) in work {
        let e = &r.base.evaluations()[i];
        let q = match row {
            Some(row) => &e.rows[row].cases[case],
            None => {
                &e.uniform
                    .as_ref()
                    .ok_or_else(|| bad("uniform行がない"))?
                    .cases[case]
            }
        };
        let original = r.base.base().evaluations()[i].evaluation();
        let g = match original.outcome() {
            ObjectEvaluationOutcome::Evaluated(g) => Some(g.as_ref()),
            _ => None,
        };
        let explicit = match e.shape {
            LawNumericShape::Equality { explicit_guard, .. }
            | LawNumericShape::Unsupported { explicit_guard, .. } => explicit_guard,
        };
        let guard = guard(inputs, e.position, row, case, g, q, explicit, c)?;
        let items: Vec<_> = if q.components.is_empty() {
            vec![None]
        } else {
            q.components.iter().map(Some).collect()
        };
        for component in items {
            tick(c)?;
            let ty = component
                .map(|v| v.ty.clone())
                .unwrap_or_else(|| match &e.shape {
                    LawNumericShape::Unsupported { ty, .. }
                    | LawNumericShape::Equality { ty, .. } => ty.clone(),
                });
            let path = component.map(|v| v.path.clone()).unwrap_or_default();
            let mut occurrence = EquationOccurrence {
                position: e.position,
                row,
                case,
                component: path.clone(),
                ty: ty.clone(),
                required: q.reading.required(),
                guard: guard.clone(),
                evaluation: q.evaluation,
                operands: q.operand_evaluations.clone(),
                epsilon_producer: q.epsilon_producer,
                ring: None,
                left: None,
                right: None,
                nu: None,
                epsilon: component.and_then(|v| v.epsilon.clone()),
                residual: component.and_then(|v| v.residual.clone()),
                evaluated_nu: None,
                epsilon_constant: component
                    .and_then(|v| v.epsilon.as_ref())
                    .map(|v| EquationPolynomial::constant(v.scalar().clone(), c))
                    .transpose()?,
                residual_constant: component
                    .and_then(|v| v.residual.as_ref())
                    .map(|v| EquationPolynomial::constant(v.scalar().clone(), c))
                    .transpose()?,
                component_holds: None,
                steps: vec![],
                status: match guard {
                    EquationGuard::OutsideObject | EquationGuard::AlwaysFalse => {
                        EquationPresentationStatus::NotApplicable
                    }
                    EquationGuard::Undetermined => EquationPresentationStatus::Undetermined,
                    _ => EquationPresentationStatus::UnsupportedAlgorithm,
                },
            };
            if component.is_some() {
                let index = ring(&mut r.rings, &ty, c)?;
                occurrence.ring = Some(index);
                if matches!(
                    guard,
                    EquationGuard::OutsideObject | EquationGuard::AlwaysFalse
                ) {
                    // 適用外/guard偽でも原式の記号表示は残す。通常評価を実行したことにはせず、
                    // 生差εは未生成のまま、適用条件付きresidualの零と区別する。
                    if let LawNumericShape::Equality { left, right, .. } = e.shape
                        && let Some((lhs, rhs)) = source_polynomial::operands(
                            inputs,
                            original.instance(),
                            left,
                            right,
                            &path,
                            &mut r.rings[index],
                            c,
                        )?
                    {
                        occurrence.nu = Some(lhs.binary(BinOp::Sub, &rhs, c)?);
                        occurrence.left = Some(lhs);
                        occurrence.right = Some(rhs);
                    }
                    if occurrence.nu.is_none() && row.is_none() {
                        // 同じ元instanceの全域正規化だけを共有する。対象外でbodyを実行しない。
                        for source in r.base.base().evaluations() {
                            tick(c)?;
                            if source.position().instance != e.position.instance { continue; }
                            if let Some((_, _, value)) = super::object_law_transport::constant_numeric_family(source.evaluation(), c)? {
                                occurrence.nu = Some(EquationPolynomial::constant(value, c)?);
                                break;
                            }
                        }
                    }
                    occurrence.status = EquationPresentationStatus::NotApplicable;
                } else if row.is_none()
                    && let Some((_, _, value)) = super::object_law_transport::constant_numeric_family(original, c)? {
                    let polynomial = EquationPolynomial::constant(value.clone(), c)?;
                    occurrence.nu = Some(polynomial);
                    occurrence.evaluated_nu = Some(NumericTransportValue::observed(value.clone()));
                    occurrence.component_holds = Some(value == numeric::zero(&ty, c).map_err(invalid)?);
                    occurrence.status = EquationPresentationStatus::Ready;
                    if occurrence.required && guard == EquationGuard::AlwaysTrue {
                        r.rings[index].required_generators.push(r.occurrences.len());
                    }
                } else if let (Some(g), [l, rhs]) = (g, q.operand_evaluations.as_slice()) {
                    let mut compiler = Compiler {
                        inputs,
                        g,
                        ring: &mut r.rings[index],
                        position: e.position,
                        row,
                        case,
                        steps: vec![],
                    };
                    if let Some(root) = q.evaluation {
                        compiler.collect_support(NodeRef(root), c)?;
                    }
                    occurrence.left = compiler.compile(NodeRef(*l), &path, c)?;
                    occurrence.right = compiler.compile(NodeRef(*rhs), &path, c)?;
                    occurrence.steps = compiler.steps;
                    if let (Some(l), Some(rhs)) = (&occurrence.left, &occurrence.right) {
                        let nu = l.binary(BinOp::Sub, rhs, c)?;
                        let values: Vec<_> = r.rings[index]
                            .symbols
                            .iter()
                            .map(|s| {
                                s.readings
                                    .iter()
                                    .rev()
                                    .find(|v| {
                                        v.position == e.position && v.row == row && v.case == case
                                    })
                                    .and_then(|v| v.assignment.clone())
                                    .or_else(|| s.value.clone())
                            })
                            .collect();
                        let evaluated = nu.evaluate(&values, c)?;
                        if let Some(epsilon) = &occurrence.epsilon {
                            if evaluated.as_ref() != Some(epsilon) {
                                return Err(bad("evA(ν)が元Evaluatorのεと違う"));
                            }
                            let zero = NumericTransportValue::observed(
                                numeric::zero(&ty, c).map_err(invalid)?,
                            );
                            let holds = epsilon == &zero;
                            if component
                                .and_then(|v| v.left.as_ref().zip(v.right.as_ref()))
                                .is_none_or(|(a, b)| (a == b) != holds)
                            {
                                return Err(bad("元成分等号とε零性が違う"));
                            }
                            occurrence.component_holds = Some(holds);
                            occurrence.evaluated_nu = evaluated;
                        }
                        occurrence.nu = Some(nu);
                        occurrence.status = if guard == EquationGuard::AlwaysFalse {
                            EquationPresentationStatus::NotApplicable
                        } else if guard == EquationGuard::StateDependent {
                            EquationPresentationStatus::UnsupportedAlgorithm
                        } else if guard == EquationGuard::Undetermined
                            || occurrence.epsilon.is_none()
                            || r.rings[index].symbols.iter().any(|s| s.value.is_none())
                        {
                            EquationPresentationStatus::Undetermined
                        } else {
                            EquationPresentationStatus::Ready
                        };
                        if occurrence.required && guard == EquationGuard::AlwaysTrue {
                            r.rings[index].required_generators.push(r.occurrences.len());
                        }
                    }
                } else {
                    if let (Some(g), Some(root)) = (g, q.evaluation) {
                        Compiler {
                            inputs,
                            g,
                            ring: &mut r.rings[index],
                            position: e.position,
                            row,
                            case,
                            steps: vec![],
                        }
                        .collect_support(NodeRef(root), c)?;
                    }
                    occurrence.status = if guard == EquationGuard::AlwaysFalse {
                        EquationPresentationStatus::NotApplicable
                    } else if guard == EquationGuard::StateDependent {
                        EquationPresentationStatus::UnsupportedAlgorithm
                    } else {
                        EquationPresentationStatus::Undetermined
                    };
                }
            }
            r.occurrences.push(occurrence);
            if r.occurrences.len() == count {
                r.complete = families_complete;
            }
            c.checkpoint(Checkpoint::EquationPresentationRow)
                .map_err(ConstructionFailure::from)?;
        }
    }
    r.complete = families_complete;
    tick(c)
}
pub fn object_equation_presentation(
    inputs: Arc<CheckedInputs>,
    reading: &str,
    snapshot: &str,
    root: &str,
    object: usize,
    c: &mut Control,
) -> Result<EquationPresentation, EquationPresentationFailure> {
    let base = object_law_residuals(Arc::clone(&inputs), reading, snapshot, root, c)
        .map_err(EquationPresentationFailure::Original)?;
    if object >= base.base().readings().objects().len() {
        return Err(EquationPresentationFailure::Selection(
            ConstructionFailure::InvalidSelection("方程式表示の対象添字が域外".into()),
        ));
    }
    let mut r = EquationPresentation {
        base,
        object,
        rings: vec![],
        occurrences: vec![],
        complete: false,
    };
    match populate(&mut r, &inputs, c) {
        Ok(()) => Ok(r),
        Err(cause) => Err(EquationPresentationFailure::Reading {
            cause,
            partial: Box::new(r),
        }),
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::input::{InputSources, check_inputs};

    fn inputs() -> Arc<CheckedInputs> {
        inputs_with("law required amount(c:Part):c.quantity+1=0;")
    }
    fn inputs_with(body: &str) -> Arc<CheckedInputs> {
        let d = crate::definition::check_definitions(&[("definition0", fixture::D.as_bytes())])
            .unwrap();
        let digest = &d.vocabularies["Pattern"].digest;
        let law = format!(
            "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";{body}}}"
        );
        Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![fixture::D.as_bytes().to_vec()],
                    law.into_bytes(),
                    fixture::A.replace("@DIGEST@", digest).into_bytes(),
                ),
                &mut Control::unlimited(),
            )
            .unwrap(),
        )
    }
    #[test]
    fn uniform_numeric_difference_retains_full_parameters_and_rejects_changed_residual() {
        for ty in [Type::Z, Type::Q] {
            let name = if ty == Type::Z { "Z" } else { "Q" };
            let inputs = inputs_with(&format!("law required balanced(c:Part,n:{name},m:{name}):let a=n+m in a=n+m+1;"));
            let mut c = Control::unlimited();
            let mut presentation = object_equation_presentation(inputs.clone(), "Selected", "v", "root", 0, &mut c).unwrap();
            assert_eq!(presentation.status(), EquationPresentationStatus::Ready);
            assert!(!presentation.occurrences.is_empty());
            let one = numeric::literal("1", &ty, &c).unwrap();
            let expected = NumericTransportValue::observed(numeric::unary(UnOp::Neg, &one, &c).unwrap());
            for occurrence in &presentation.occurrences {
                assert_eq!(occurrence.epsilon.as_ref(), Some(&expected));
                assert_eq!(occurrence.residual.as_ref(), Some(&expected));
                assert_eq!(occurrence.component_holds, Some(false));
                assert_eq!(occurrence.nu.as_ref().unwrap().evaluate(&[], &mut c).unwrap(), Some(expected.clone()));
                assert!(occurrence.row.is_none());
            }
            for source in presentation.base.base().evaluations() {
                assert_eq!(source.evaluation().instance().parameters().len(), 2);
                assert!(source.family().rows().is_empty());
                assert!(source.family().domains().is_empty());
                assert!(source.family().uniform().is_some());
            }
            presentation.recheck(inputs.clone(), &mut c).unwrap();
            presentation.occurrences[0].nu = Some(EquationPolynomial::constant(numeric::zero(&ty, &c).unwrap(), &mut c).unwrap());
            assert!(presentation.recheck(inputs, &mut c).is_err());
        }
    }
    #[test]
    fn numeric_family_uniformity_is_not_inferred_from_false_or_observed_values() {
        for body in [
            "law required varying(c:Part,n:Z):n=0;",
            "law required varying(c:Part,n:Z):n+c.quantity=n;",
            "law required varying(c:Part,n:Z) when false:n=n;",
            "law required varying(c:Part,n:Z) when n=0:n=n;",
            "law required varying(c:Part,n:Z) when c.quantity=0:n=n;",
        ] {
            let inputs = inputs_with(body);
            let mut c = Control::unlimited();
            let profiles = crate::construction::profiles::construct_profiles(&inputs, "Selected", "v", "root", &mut c).unwrap();
            let readings = crate::construction::readings::object_reading_instances(&inputs, profiles.construction(), &mut c).unwrap();
            let evaluation = super::super::object_evaluate::evaluate_object_instance(inputs.clone(), &readings, 0, 0, &mut c).unwrap();
            assert!(super::super::object_law_transport::constant_numeric_family(&evaluation, &mut c).unwrap().is_none());
        }
    }
    #[test]
    fn uniform_true_guard_preserves_numeric_difference() {
        for (ty, guard) in [("Z", "true"), ("Q", "let a=n+1 in a=n+1")] {
            let inputs = inputs_with(&format!("law required balanced(c:Part,n:{ty}) when {guard}:n=n+1;"));
            let mut c = Control::unlimited();
            let presentation = object_equation_presentation(inputs.clone(), "Selected", "v", "root", 0, &mut c).unwrap();
            assert_eq!(presentation.status(), EquationPresentationStatus::Ready);
            let ty = if ty == "Z" { Type::Z } else { Type::Q };
            let one = numeric::literal("1", &ty, &c).unwrap();
            let expected = NumericTransportValue::observed(numeric::unary(UnOp::Neg, &one, &c).unwrap());
            let mut applicable = 0;
            for occurrence in &presentation.occurrences {
                if occurrence.guard == EquationGuard::OutsideObject { continue; }
                applicable += 1;
                assert_eq!(occurrence.guard, EquationGuard::AlwaysTrue);
                assert_eq!(occurrence.component_holds, Some(false));
                assert_eq!(occurrence.epsilon.as_ref(), Some(&expected));
                assert_eq!(occurrence.nu.as_ref().unwrap().evaluate(&[], &mut c).unwrap(), Some(expected.clone()));
            }
            assert!(applicable > 0);
            presentation.recheck(inputs, &mut c).unwrap();
        }
    }
    #[test]
    fn uniform_rational_literal_difference_is_exact() {
        let inputs = inputs_with("law required balanced(c:Part,n:Q):n+rat(1,2)=n+rat(1,3);");
        let mut c = Control::unlimited();
        let presentation = object_equation_presentation(inputs.clone(), "Selected", "v", "root", 0, &mut c).unwrap();
        assert_eq!(presentation.status(), EquationPresentationStatus::Ready);
        let expected = NumericTransportValue::observed(numeric::rational(&Scalar::Z(1.into()), &Scalar::Z(6.into()), &c).unwrap());
        assert!(!presentation.occurrences.is_empty());
        for occurrence in &presentation.occurrences {
            assert_eq!(occurrence.ty, Type::Q);
            assert_eq!(occurrence.epsilon.as_ref(), Some(&expected));
            assert_eq!(occurrence.nu.as_ref().unwrap().evaluate(&[], &mut c).unwrap(), Some(expected.clone()));
        }
        presentation.recheck(inputs, &mut c).unwrap();
    }
    #[test]
    fn recheck_rejects_forged_symbols_polynomials_ideal_substitution_origin_and_status() {
        let i = inputs();
        for mode in 0..28 {
            let mut r = object_equation_presentation(
                i.clone(),
                "Selected",
                "v",
                "root",
                0,
                &mut Control::unlimited(),
            )
            .unwrap();
            match mode {
                0 => r.object = 1,
                1 => r.complete = false,
                2 => r.rings[0].ty = Type::Q,
                3 => r.rings[0].symbols[0].slot.subject = "root".into(),
                4 => r.rings[0].symbols[0].slot.component = vec![1],
                5 => r.rings[0].symbols[0].value = None,
                6 => r.rings[0].symbols[0].readings[0].evaluation += 1,
                7 => r.rings[0].symbols[0].readings[0].fact.atom = None,
                8 => r.rings[0].required_generators.clear(),
                9 => r.occurrences[0].position.instance += 1,
                10 => r.occurrences[0].component = vec![1],
                11 => r.occurrences[0].guard = EquationGuard::StateDependent,
                12 => r.occurrences[0].required = false,
                13 => {
                    r.occurrences[0].nu.as_mut().unwrap().terms[0].coefficient =
                        NumericTransportValue::observed(Scalar::Z(0.into()))
                }
                14 => r.occurrences[0].nu.as_mut().unwrap().terms[1].variables = vec![0, 0],
                15 => r.occurrences[0].epsilon = None,
                16 => r.occurrences[0].evaluated_nu = None,
                17 => r.occurrences[0].epsilon_producer = None,
                18 => r.occurrences[0].operands.reverse(),
                19 => r.occurrences[0].steps.clear(),
                20 => r.occurrences[0].component_holds = Some(true),
                21 => r.occurrences[0].status = EquationPresentationStatus::Undetermined,
                22 => r.rings[0].symbols[0].readings[0].assignment = None,
                23 => r.occurrences[0].nu.as_mut().unwrap().ty = Type::Q,
                24 => r.rings[0].evaluation_images = None,
                25 => r.occurrences[0].epsilon_constant = None,
                26 => r.occurrences[0].residual_constant = None,
                _ => r.rings[0].symbols[0].readings.clear(),
            }
            assert!(
                matches!(
                    r.recheck(i.clone(), &mut Control::unlimited()),
                    Err(EquationPresentationFailure::Reading {
                        cause: ConstructionFailure::Inconsistent(_),
                        ..
                    })
                ),
                "mode {mode}"
            );
        }
    }
}

#[cfg(test)]
#[path = "../../tests/common/object_view_compatibility_data.rs"]
mod fixture;
