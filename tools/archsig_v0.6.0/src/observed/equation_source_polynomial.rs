//! 未実行の原式を同じ型付きASTから多項式へ翻訳する。原式の評価値は生成しない。
use super::*;
use crate::observed::affine;
use crate::{archmap::Slot, construction::readings::ObjectInstance, law::model::Signature};
use std::{collections::BTreeMap, sync::Arc};

#[derive(Clone)]
enum Binding {
    Reference {
        snapshot: String,
        subject: String,
    },
    Polynomial(EquationPolynomial),
    ParameterForm(affine::Form),
    Sum { polynomial: EquationPolynomial, parameters: affine::Form },
    Tuple(Vec<Binding>),
    Lexical {
        expression: usize,
        variables: Arc<BTreeMap<String, Binding>>,
    },
}
impl Binding {
    fn affine(&self, c: &mut Control) -> Result<Option<affine::Form>, ConstructionFailure> {
        match self {
            Self::ParameterForm(value) => Ok(Some(value.clone())),
            Self::Polynomial(value) if value.terms.iter().all(|term| term.variables.is_empty()) => {
                let Some(value) = value.evaluate(&[], c)? else { return Ok(None) };
                affine::constant(value.scalar(), c).map_err(invalid)
            }
            Self::Sum { polynomial, parameters } if polynomial.terms.iter().all(|term| term.variables.is_empty()) => {
                let Some(value) = polynomial.evaluate(&[], c)? else { return Ok(None) };
                let constant = affine::constant(value.scalar(), c).map_err(invalid)?;
                affine::binary(BinOp::Add, constant.as_ref(), Some(parameters), c).map_err(invalid)
            }
            _ => Ok(None),
        }
    }
    fn binary(&self, op: BinOp, rhs: &Self, c: &mut Control) -> Result<Option<Self>, ConstructionFailure> {
        if let (Self::Polynomial(left), Self::Polynomial(right)) = (self, rhs) {
            return Ok(Some(Self::Polynomial(left.binary(op, right, c)?)));
        }
        if let Some(value) = affine::binary(op, self.affine(c)?.as_ref(), rhs.affine(c)?.as_ref(), c).map_err(invalid)? {
            return Ok(Some(Self::ParameterForm(value)));
        }
        if !matches!(op, BinOp::Add | BinOp::Sub) { return Ok(None); }
        let (Some((left, a)), Some((right, b))) = (self.split(c)?, rhs.split(c)?) else { return Ok(None) };
        let Some(parameters) = affine::binary(op, Some(&a), Some(&b), c).map_err(invalid)? else { return Ok(None) };
        Ok(Some(Self::Sum { polynomial: left.binary(op, &right, c)?, parameters }))
    }
    fn split(&self, c: &mut Control) -> Result<Option<(EquationPolynomial, affine::Form)>, ConstructionFailure> {
        Ok(match self {
            Self::Sum { polynomial, parameters } => Some((polynomial.clone(), parameters.clone())),
            Self::Polynomial(polynomial) => {
                let zero = numeric::zero(&polynomial.ty, c).map_err(invalid)?;
                affine::constant(&zero, c).map_err(invalid)?.map(|form| (polynomial.clone(), form))
            }
            Self::ParameterForm(form) => {
                let zero = numeric::zero(&form.ty(c).map_err(invalid)?, c).map_err(invalid)?;
                Some((EquationPolynomial::constant(zero, c)?, form.clone()))
            }
            _ => None,
        })
    }
}
struct Compiler<'a> {
    inputs: &'a CheckedInputs,
    ring: &'a mut EquationRing,
    variables: BTreeMap<String, Binding>,
}
impl Compiler<'_> {
    // Scalar環への翻訳は使用箇所のcomponent pathが判明してから行う。
    // initializerの環境を保存し、後続letやhelperの局所名を捕獲しない。
    fn lexical(&self, expression: usize) -> Binding {
        Binding::Lexical {
            expression,
            variables: Arc::new(self.variables.clone()),
        }
    }
    fn bind_match(
        &mut self,
        scrutinee: usize,
        arms: &[crate::law::ast::Arm],
        c: &mut Control,
    ) -> Result<Option<usize>, ConstructionFailure> {
        let Some(body) = super::super::object_law_residuals::binding_match_body(
            self.inputs,
            scrutinee,
            arms,
            c,
        )?
        else {
            return Ok(None);
        };
        if let crate::law::ast::Pattern::Name(name) = &arms[0].pattern {
            let value = self.lexical(scrutinee);
            self.variables.insert(name.name.clone(), value);
        }
        Ok(Some(body))
    }
    // Lawのratは整数literal二つだけを許す。既存の正確な数値構成を再利用する。
    fn integer_literal(&self, id: usize, c: &mut Control) -> Result<Scalar, ConstructionFailure> {
        let ExprKind::Int(value) = &self.inputs.law().exprs[id].kind else {
            return Err(bad("型検査済みratの引数が整数literalでない"));
        };
        numeric::literal(value, &Type::Z, c).map_err(invalid)
    }
    fn binding(
        &mut self,
        value: Binding,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<Binding>, ConstructionFailure> {
        tick(c)?;
        match value {
            Binding::Lexical {
                expression,
                variables,
            } => {
                let previous = std::mem::replace(&mut self.variables, (*variables).clone());
                let result = self.expression(expression, path, c);
                self.variables = previous;
                result
            }
            Binding::Tuple(items) if !path.is_empty() => {
                let item = items
                    .get(path[0])
                    .cloned()
                    .ok_or_else(|| bad("原式のtuple束縛が範囲外"))?;
                self.binding(item, &path[1..], c)
            }
            value if path.is_empty() => Ok(Some(value)),
            _ => Ok(None),
        }
    }
    fn field(
        &mut self,
        reference: Binding,
        name: &str,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<Binding>, ConstructionFailure> {
        tick(c)?;
        let Binding::Reference { snapshot, subject } = reference else {
            return Ok(None);
        };
        let selected = self
            .inputs
            .archmap()
            .snapshots
            .iter()
            .find(|s| s.id == snapshot)
            .and_then(|s| s.subjects.iter().find(|s| s.id == subject))
            .ok_or_else(|| bad("原式の固定参照先がない"))?;
        let field = format!("{}.{name}", selected.ty);
        let selected = selected
            .fields
            .iter()
            .find(|f| f.name == field)
            .ok_or_else(|| bad("原式の固定fieldがない"))?;
        if let (Slot::Known { value, .. }, Type::Ref(_) | Type::Owned(..)) =
            (&selected.slot, &selected.ty)
            && let crate::archmap::Value::Ref { snapshot, subject } = value
        {
            return Ok(Some(Binding::Reference {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
            }));
        }
        let mut ty = &selected.ty;
        for &i in path {
            let Type::Tuple(items) = ty else {
                return Ok(None);
            };
            ty = items.get(i).ok_or_else(|| bad("原式fieldの成分が範囲外"))?;
        }
        if ty != &self.ring.ty {
            return Ok(None);
        }
        let observed = match &selected.slot {
            Slot::Known { value, .. } => numeric::from_input(value, &selected.ty, c)
                .map_err(invalid)?
                .and_then(|v| projected(&v, path))
                .map(NumericTransportValue::observed),
            Slot::Missing => None,
        };
        let slot = EquationSlot {
            snapshot,
            subject,
            field,
            component: path.to_vec(),
        };
        let position = if let Some(i) = self.ring.symbols.iter().position(|s| s.slot == slot) {
            if self.ring.symbols[i].value != observed {
                return Err(bad("原式の同じslotに異なる観測値がある"));
            }
            i
        } else {
            if let Some(value) = &observed {
                if let Some(images) = &mut self.ring.evaluation_images {
                    images.push(EquationPolynomial::constant(value.scalar().clone(), c)?);
                }
            } else {
                self.ring.evaluation_images = None;
            }
            self.ring.symbols.push(EquationSymbol {
                slot,
                value: observed,
                // 未実行の式に、架空の元Evaluation参照を与えない。
                readings: vec![],
            });
            self.ring.symbols.len() - 1
        };
        Ok(Some(Binding::Polynomial(EquationPolynomial::variable(
            &self.ring.ty,
            position,
            c,
        )?)))
    }
    fn expression(
        &mut self,
        id: usize,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<Binding>, ConstructionFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            let expression = self
                .inputs
                .law()
                .exprs
                .get(id)
                .ok_or_else(|| bad("原式IDがない"))?;
            Ok(match &expression.kind {
                ExprKind::Group(child) => self.expression(*child, path, c)?,
                ExprKind::Int(n) if path.is_empty() => {
                    let ty = self
                        .inputs
                        .law()
                        .expr_type(id)
                        .ok_or_else(|| bad("原式の数値型がない"))?;
                    if ty != &self.ring.ty {
                        return Ok(None);
                    }
                    Some(Binding::Polynomial(EquationPolynomial::constant(
                        numeric::literal(n, ty, c).map_err(invalid)?,
                        c,
                    )?))
                }
                ExprKind::Dotted(names) => {
                    let Some(first) = names.first() else {
                        return Ok(None);
                    };
                    let Some(value) = self.variables.get(&first.name).cloned() else {
                        return Ok(None);
                    };
                    if names.len() == 1 {
                        return self.binding(value, path, c);
                    }
                    let Some(mut value) = self.binding(value, &[], c)? else {
                        return Ok(None);
                    };
                    for (i, name) in names.iter().enumerate().skip(1) {
                        let tail = if i + 1 == names.len() { path } else { &[] };
                        let Some(next) = self.field(value, &name.name, tail, c)? else {
                            return Ok(None);
                        };
                        value = next;
                    }
                    Some(value)
                }
                ExprKind::Field { base, name } => {
                    let Some(value) = self.expression(*base, &[], c)? else {
                        return Ok(None);
                    };
                    self.field(value, &name.name, path, c)?
                }
                ExprKind::Index { base, index, .. } => {
                    let mut component = vec![*index];
                    component.extend(path);
                    self.expression(*base, &component, c)?
                }
                ExprKind::Tuple(items) => {
                    if let Some((&i, tail)) = path.split_first() {
                        self.expression(
                            *items.get(i).ok_or_else(|| bad("原式tupleの成分が範囲外"))?,
                            tail,
                            c,
                        )?
                    } else {
                        let mut values = vec![];
                        for &item in items {
                            let Some(value) = self.expression(item, &[], c)? else {
                                return Ok(None);
                            };
                            values.push(value);
                        }
                        Some(Binding::Tuple(values))
                    }
                }
                ExprKind::Unary {
                    op: UnOp::Neg,
                    operand,
                } => {
                    let Some(value) = self.expression(*operand, path, c)?
                    else {
                        return Ok(None);
                    };
                    let zero = EquationPolynomial::constant(
                        numeric::zero(&self.ring.ty, c).map_err(invalid)?,
                        c,
                    )?;
                    Binding::Polynomial(zero).binary(BinOp::Sub, &value, c)?
                }
                ExprKind::Binary {
                    op: op @ (BinOp::Add | BinOp::Sub | BinOp::Mul),
                    lhs,
                    rhs,
                } => {
                    let Some(left) = self.expression(*lhs, path, c)? else {
                        return Ok(None);
                    };
                    let Some(right) = self.expression(*rhs, path, c)? else {
                        return Ok(None);
                    };
                    left.binary(*op, &right, c)?
                }
                ExprKind::Match { scrutinee, arms } => {
                    let previous = self.variables.clone();
                    let Some(body) = self.bind_match(*scrutinee, arms, c)? else {
                        return Ok(None);
                    };
                    let result = self.expression(body, path, c);
                    self.variables = previous;
                    result?
                }
                ExprKind::Let { name, value, body } => {
                    let value = self.lexical(*value);
                    let previous = self.variables.insert(name.name.clone(), value);
                    let result = self.expression(*body, path, c);
                    if let Some(previous) = previous {
                        self.variables.insert(name.name.clone(), previous);
                    } else {
                        self.variables.remove(&name.name);
                    }
                    result?
                }
                ExprKind::Call { callee, args } => {
                    let mut callee = *callee;
                    while let ExprKind::Group(inner) = self.inputs.law().exprs[callee].kind {
                        tick(c)?;
                        callee = inner;
                    }
                    if let ExprKind::Dotted(names) = &self.inputs.law().exprs[callee].kind
                        && names.len() == 1
                        && names[0].name == "rat"
                    {
                        if self.ring.ty != Type::Q || !path.is_empty() || args.len() != 2 {
                            return Ok(None);
                        }
                        let numerator = self.integer_literal(args[0], c)?;
                        let denominator = self.integer_literal(args[1], c)?;
                        let value =
                            numeric::rational(&numerator, &denominator, c).map_err(invalid)?;
                        return Ok(Some(Binding::Polynomial(EquationPolynomial::constant(
                            value, c,
                        )?)));
                    }
                    let span = self.inputs.law().exprs[callee].span;
                    let target = self.inputs.law().infos.iter().find_map(|info| {
                        info.references
                            .iter()
                            .find_map(|(at, name)| (*at == span).then_some(name))
                    });
                    let Some(target) = target else {
                        return Ok(None);
                    };
                    let declaration = self
                        .inputs
                        .law()
                        .declarations
                        .get(target)
                        .ok_or_else(|| bad("原式helperの宣言がない"))?;
                    let Signature::View { params, body, .. } = &declaration.signature else {
                        return Ok(None);
                    };
                    if params.len() != args.len()
                        || params.iter().any(|p| matches!(p.ty, Type::Owned(..)))
                    {
                        return Ok(None);
                    }
                    let mut bindings = BTreeMap::new();
                    for (parameter, argument) in params.iter().zip(args) {
                        bindings.insert(parameter.name.clone(), self.lexical(*argument));
                    }
                    let previous = std::mem::replace(&mut self.variables, bindings);
                    let result = self.expression(*body, path, c);
                    self.variables = previous;
                    result?
                }
                _ => None,
            })
        })
    }
}

pub(super) struct SourceDifference {
    pub left: Option<EquationPolynomial>,
    pub right: Option<EquationPolynomial>,
    pub difference: EquationPolynomial,
}
/// 各parameter代入でK[X]の元を返す。parameterを観測slotへ混ぜない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct PolynomialFamily {
    pub constant: EquationPolynomial,
    pub parameters: Vec<(affine::Parameter, Scalar)>,
}
impl PolynomialFamily {
    pub(super) fn at(&self, values: &[(affine::Parameter, Scalar)], c: &mut Control) -> Result<EquationPolynomial, ConstructionFailure> {
        let mut assignments = BTreeMap::new();
        for (parameter, value) in values {
            tick(c)?;
            if value.ty() != parameter.kind.ty() || assignments.insert(parameter, value).is_some() {
                return Err(bad("数値関数族の引数型または重複が不正"));
            }
        }
        let mut result = self.constant.clone();
        for (parameter, coefficient) in &self.parameters {
            tick(c)?;
            let value = assignments.get(parameter).ok_or_else(|| bad("数値関数族の元parameter代入がない"))?;
            let term = numeric::binary(BinOp::Mul, coefficient, value, c).map_err(invalid)?;
            result = result.binary(BinOp::Add, &EquationPolynomial::constant(term, c)?, c)?;
        }
        Ok(result)
    }
    fn from_binding(value: &Binding, c: &mut Control) -> Result<Option<Self>, ConstructionFailure> {
        let Some((polynomial, form)) = value.split(c)? else { return Ok(None) };
        let Some((constant, parameters)) = form.parameter_coordinates(c).map_err(invalid)? else { return Ok(None) };
        Ok(Some(Self { constant: polynomial.binary(BinOp::Add, &EquationPolynomial::constant(constant, c)?, c)?, parameters }))
    }
    fn constant_polynomial(self) -> Option<EquationPolynomial> {
        self.parameters.is_empty().then_some(self.constant)
    }
}
pub(super) struct SourceFamilyDifference {
    pub left: PolynomialFamily,
    pub right: PolynomialFamily,
    pub difference: PolynomialFamily,
}
pub(super) fn operands(
    inputs: &CheckedInputs,
    instance: &ObjectInstance,
    left: usize,
    right: usize,
    path: &[usize],
    ring: &mut EquationRing,
    c: &mut Control,
) -> Result<Option<SourceDifference>, ConstructionFailure> {
    let mut candidate = ring.clone();
    let Some(source) = family_operands(inputs, instance, left, right, path, &mut candidate, c)? else { return Ok(None) };
    let Some(difference) = source.difference.constant_polynomial() else { return Ok(None) };
    *ring = candidate;
    Ok(Some(SourceDifference { left: source.left.constant_polynomial(), right: source.right.constant_polynomial(), difference }))
}
pub(super) fn family_operands(
    inputs: &CheckedInputs,
    instance: &ObjectInstance,
    left: usize,
    right: usize,
    path: &[usize],
    ring: &mut EquationRing,
    c: &mut Control,
) -> Result<Option<SourceFamilyDifference>, ConstructionFailure> {
    let mut variables: BTreeMap<_, _> = instance
        .bindings()
        .iter()
        .map(|b| {
            (
                b.parameter().name.clone(),
                Binding::Reference {
                    snapshot: b.subject().snapshot.clone(),
                    subject: b.subject().subject.clone(),
                },
            )
        })
        .collect();
    // 未束縛parameterは観測slotではない。独立の元binder軸のまま計算し、
    // 差から全軸が消えた場合だけK[X]へ移す。具体値の代入は行わない。
    for parameter in instance.parameters() {
        tick(c)?;
        let kind = match parameter.ty {
            Type::Z => affine::NumberType::Z,
            Type::Q => affine::NumberType::Q,
            _ => continue,
        };
        let key = affine::Parameter { binder: parameter.span, name: parameter.name.clone(),
            context: Default::default(), kind };
        if let Some(value) = affine::parameter(&parameter.ty, &key, c).map_err(invalid)? {
            variables.insert(parameter.name.clone(), Binding::ParameterForm(value));
        }
    }
    let mut candidate = ring.clone();
    let mut compiler = Compiler {
        inputs,
        ring: &mut candidate,
        variables,
    };
    // shapeは外側のlet/matchを除いた左右を指す。元bodyから同じlexical束縛を
    // 順に復元してから翻訳し、局所名を未束縛の原始変数に変えない。
    let Signature::Law { body, .. } = &inputs
        .law()
        .declarations
        .get(&instance.declaration().name)
        .ok_or_else(|| bad("原式のLaw宣言がない"))?
        .signature
    else {
        return Err(bad("原式の宣言がLawでない"));
    };
    let mut cursor = *body;
    loop {
        tick(c)?;
        match &inputs.law().exprs[cursor].kind {
            ExprKind::Group(child) => cursor = *child,
            ExprKind::Let { name, value, body } => {
                let value = compiler.lexical(*value);
                compiler.variables.insert(name.name.clone(), value);
                cursor = *body;
            }
            ExprKind::Match { scrutinee, arms } => {
                let Some(body) = compiler.bind_match(*scrutinee, arms, c)? else {
                    return Ok(None);
                };
                cursor = body;
            }
            _ => break,
        }
    }
    let Some(left) = compiler.expression(left, path, c)? else {
        return Ok(None);
    };
    let Some(right) = compiler.expression(right, path, c)? else {
        return Ok(None);
    };
    let Some(difference) = left.binary(BinOp::Sub, &right, c)? else { return Ok(None) };
    let (Some(left), Some(right), Some(difference)) = (
        PolynomialFamily::from_binding(&left, c)?,
        PolynomialFamily::from_binding(&right, c)?,
        PolynomialFamily::from_binding(&difference, c)?,
    ) else { return Ok(None) };
    let result = SourceFamilyDifference { left, right, difference };
    *ring = candidate;
    Ok(Some(result))
}
