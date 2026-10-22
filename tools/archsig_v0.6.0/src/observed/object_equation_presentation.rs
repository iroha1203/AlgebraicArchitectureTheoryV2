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
                ExprKind::Field { name, .. } => self.field(r, &name.name, path, c)?,
                ExprKind::Dotted(names) if names.len() > 1 => {
                    self.field(r, &names[names.len() - 1].name, path, c)?
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
    g: Option<&ObservedEvaluation>,
    case: &LawResidualCase,
    explicit: bool,
    c: &mut Control,
) -> Result<EquationGuard, ConstructionFailure> {
    tick(c)?;
    match case.reading.application() {
        LawApplication::OutsideObject => return Ok(EquationGuard::OutsideObject),
        LawApplication::ConditionalMembership(_) => return Ok(EquationGuard::Undetermined),
        LawApplication::Guard(None) => return Ok(EquationGuard::Undetermined),
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
    for (i, e) in r.base.evaluations().iter().enumerate() {
        tick(c)?;
        if e.position.object != r.object {
            continue;
        }
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
        let guard = guard(g, q, explicit, c)?;
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
                status: EquationPresentationStatus::UnsupportedAlgorithm,
            };
            if component.is_some() {
                let index = ring(&mut r.rings, &ty, c)?;
                occurrence.ring = Some(index);
                if guard == EquationGuard::OutsideObject {
                    occurrence.status = EquationPresentationStatus::NotApplicable;
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
                r.complete = true;
            }
            c.checkpoint(Checkpoint::EquationPresentationRow)
                .map_err(ConstructionFailure::from)?;
        }
    }
    r.complete = true;
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
        let d = crate::definition::check_definitions(&[("definition0", fixture::D.as_bytes())])
            .unwrap();
        let digest = &d.vocabularies["Pattern"].digest;
        let law = format!(
            "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";law required amount(c:Part):c.quantity+1=0;}}"
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
    fn recheck_rejects_forged_symbols_polynomials_ideal_substitution_origin_and_status() {
        let i = inputs();
        for mode in 0..27 {
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
                _ => r.occurrences[0].residual_constant = None,
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
