//! 未実行の原式を同じ型付きASTから多項式へ翻訳する。原式の評価値は生成しない。
use super::*;
use crate::observed::affine;
use crate::{archmap::Slot, construction::readings::ObjectInstance, law::model::Signature};
use std::{collections::BTreeMap, sync::Arc};

#[derive(Clone)]
enum Binding {
    Boolean(bool),
    FiniteScalar(Scalar),
    Reference {
        snapshot: String,
        subject: String,
    },
    Polynomial(EquationPolynomial),
    ParameterForm(affine::Form),
    Family(PolynomialFamily),
    Tuple(Vec<Binding>),
    Option { element: Type, value: Option<Box<Binding>> },
    List { element: Type, items: Vec<Binding> },
    Lexical {
        expression: usize,
        variables: Arc<BTreeMap<String, Binding>>,
    },
}
impl Binding {
    fn finite_scalar(&self, c: &mut Control) -> Result<Option<Scalar>, ConstructionFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            Ok(match self {
                Self::Boolean(value) => Some(Scalar::Bool(*value)),
                Self::FiniteScalar(value) => Some(value.clone()),
                Self::Polynomial(value) if value.terms.iter().all(|term| term.variables.is_empty()) => {
                    value.evaluate(&[], c)?.map(|value| value.scalar().clone())
                }
                Self::Option { element, value } => {
                    let value = match value {
                        Some(value) => {
                            let Some(value) = value.finite_scalar(c)? else { return Ok(None) };
                            if value.ty() != *element { return Ok(None) }
                            Some(Box::new(value))
                        }
                        None => None,
                    };
                    Some(Scalar::Option { element: element.clone(), value })
                }
                Self::List { element, items } => {
                    let mut values = Vec::new();
                    for item in items {
                        let Some(value) = item.finite_scalar(c)? else { return Ok(None) };
                        if value.ty() != *element { return Ok(None) }
                        values.push(value);
                    }
                    Some(Scalar::List { element: element.clone(), items: values })
                }
                Self::Tuple(items) => {
                    let mut values = Vec::new();
                    for item in items {
                        let Some(value) = item.finite_scalar(c)? else {
                            return Ok(None);
                        };
                        values.push(value);
                    }
                    Some(Scalar::Tuple(values))
                }
                _ => None,
            })
        })
    }
    fn affine(&self, c: &mut Control) -> Result<Option<affine::Form>, ConstructionFailure> {
        match self {
            Self::ParameterForm(value) => Ok(Some(value.clone())),
            Self::Polynomial(value) if value.terms.iter().all(|term| term.variables.is_empty()) => {
                let Some(value) = value.evaluate(&[], c)? else { return Ok(None) };
                affine::constant(value.scalar(), c).map_err(invalid)
            }
            _ => Ok(None),
        }
    }
    fn binary(&self, op: BinOp, rhs: &Self, c: &mut Control) -> Result<Option<Self>, ConstructionFailure> {
        if let (Self::FiniteScalar(left), Self::FiniteScalar(right)) = (self, rhs) {
            return Ok(Some(Self::FiniteScalar(numeric::binary(op, left, right, c).map_err(invalid)?)));
        }
        if let (Self::Polynomial(left), Self::Polynomial(right)) = (self, rhs) {
            return Ok(Some(Self::Polynomial(left.binary(op, right, c)?)));
        }
        if let Some(value) = affine::binary(op, self.affine(c)?.as_ref(), rhs.affine(c)?.as_ref(), c).map_err(invalid)? {
            return Ok(Some(Self::ParameterForm(value)));
        }
        let (Some(left), Some(right)) = (PolynomialFamily::from_binding(self, c)?, PolynomialFamily::from_binding(rhs, c)?) else { return Ok(None) };
        Ok(left.binary(op, &right, c)?.map(Self::Family))
    }

    fn constant_difference(&self, rhs: &Self, c: &mut Control) -> Result<Option<EquationPolynomial>, ConstructionFailure> {
        let Some(value) = self.binary(BinOp::Sub, rhs, c)? else { return Ok(None) };
        let Some(value) = PolynomialFamily::from_binding(&value, c)? else { return Ok(None) };
        Ok((value.parameters.is_empty()
            && value.constant.terms.iter().all(|term| term.variables.is_empty()))
            .then_some(value.constant))
    }
    fn split(&self, c: &mut Control) -> Result<Option<(EquationPolynomial, affine::Form)>, ConstructionFailure> {
        Ok(match self {
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
    fn equal(
        &mut self,
        left: &Binding,
        right: &Binding,
        span: (usize, usize),
        c: &mut Control,
    ) -> Result<Option<bool>, ConstructionFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            if let (Some(left), Some(right)) = (left.finite_scalar(c)?, right.finite_scalar(c)?) {
                let Scalar::Bool(value) = super::super::environment::binary(
                    BinOp::Eq,
                    &left,
                    &right,
                    self.inputs.law(),
                    span,
                    c,
                )
                .map_err(invalid)?
                else {
                    return Err(bad("等値の結果がBoolでない"));
                };
                return Ok(Some(value));
            }
            match (left, right) {
                (Binding::Tuple(left), Binding::Tuple(right)) => {
                    if left.len() != right.len() {
                        return Err(bad("元式Tuple等値の形が違う"));
                    }
                    self.equal_components(left, right, span, c)
                }
                (
                    Binding::List {
                        element: lty,
                        items: left,
                    },
                    Binding::List {
                        element: rty,
                        items: right,
                    },
                ) => {
                    if lty != rty {
                        return Err(bad("元式List等値の要素型が違う"));
                    }
                    if left.len() != right.len() {
                        return Ok(Some(false));
                    }
                    self.equal_components(left, right, span, c)
                }
                (
                    Binding::Option {
                        element: lty,
                        value: left,
                    },
                    Binding::Option {
                        element: rty,
                        value: right,
                    },
                ) if lty == rty => match (left, right) {
                    (Some(left), Some(right)) => self.equal(left, right, span, c),
                    (None, None) => Ok(Some(true)),
                    _ => Ok(Some(false)),
                },
                (
                    Binding::Reference {
                        snapshot: ls,
                        subject: lo,
                    },
                    Binding::Reference {
                        snapshot: rs,
                        subject: ro,
                    },
                ) => Ok(Some(ls == rs && lo == ro)),
                _ => Ok(left.constant_difference(right, c)?.map(|value| value.terms.is_empty())),
            }
        })
    }
    fn equal_components(
        &mut self,
        left: &[Binding],
        right: &[Binding],
        span: (usize, usize),
        c: &mut Control,
    ) -> Result<Option<bool>, ConstructionFailure> {
        let mut known = true;
        for (left, right) in left.iter().zip(right) {
            match self.equal(left, right, span, c)? {
                Some(false) => return Ok(Some(false)),
                None => known = false,
                _ => {}
            }
        }
        Ok(known.then_some(true))
    }
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
        id: usize,
        scrutinee: usize,
        arms: &[crate::law::ast::Arm],
        c: &mut Control,
    ) -> Result<Option<usize>, ConstructionFailure> {
        if let Some(body) = super::super::object_law_residuals::binding_match_body(
            self.inputs,
            scrutinee,
            arms,
            c,
        )?
        {
            if let crate::law::ast::Pattern::Name(name) = &arms[0].pattern {
                let value = self.lexical(scrutinee);
                self.variables.insert(name.name.clone(), value);
            }
            return Ok(Some(body));
        }
        let Some(input) = self.expression(scrutinee, &[], c)? else {
            return Ok(None);
        };
        let Some(value) = input.finite_scalar(c)? else {
            return Ok(None);
        };
        let Some(arm) = super::super::data::select(self.inputs.law(), id, Some(&value), c)
            .map_err(invalid)?
        else {
            return Ok(None);
        };
        for (name, value) in
            super::super::data::bindings(self.inputs.law(), id, arm, &value, c).map_err(invalid)?
        {
            let binding = match value {
                Scalar::Bool(value) => Binding::Boolean(value),
                value => Binding::FiniteScalar(value),
            };
            self.variables.insert(name, binding);
        }
        Ok(Some(
            arms.get(arm)
                .ok_or_else(|| bad("有限matchの選択armがない"))?
                .body,
        ))
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
            Binding::FiniteScalar(Scalar::Tuple(ref items)) if !path.is_empty() => {
                let value = items.get(path[0]).cloned().ok_or_else(|| bad("有限tupleの成分が範囲外"))?;
                let value = match value { Scalar::Bool(value) => Binding::Boolean(value), value => Binding::FiniteScalar(value) };
                self.binding(value, &path[1..], c)
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
            if path.is_empty()
                && let Some(Type::Data(family)) = self.inputs.law().expr_type(id)
                && let Some((constructor, arguments)) =
                    super::super::data::expression(self.inputs.law(), id, c).map_err(invalid)?
            {
                let types = super::super::data::constructor(self.inputs.law(), family, &constructor, c)
                    .map_err(invalid)?
                    .arguments
                    .clone();
                let mut args = Vec::new();
                for (argument, ty) in arguments.iter().zip(types) {
                    let Some(binding) = self.expression(*argument, &[], c)? else {
                        return Ok(None);
                    };
                    let Some(value) = binding.finite_scalar(c)? else {
                        return Ok(None);
                    };
                    if value.ty() != ty {
                        return Ok(None);
                    }
                    args.push(value);
                }
                return Ok(Some(Binding::FiniteScalar(Scalar::Data {
                    family: family.clone(),
                    constructor,
                    args,
                })));
            }
            Ok(match &expression.kind {
                ExprKind::Group(child) => self.expression(*child, path, c)?,
                ExprKind::Int(n) if path.is_empty() => {
                    let ty = self
                        .inputs
                        .law()
                        .expr_type(id)
                        .ok_or_else(|| bad("原式の数値型がない"))?;
                    if ty != &self.ring.ty {
                        return if matches!(ty, Type::Z | Type::Q | Type::Fp(_)) {
                            Ok(Some(Binding::FiniteScalar(numeric::literal(n, ty, c).map_err(invalid)?)))
                        } else { Ok(None) };
                    }
                    Some(Binding::Polynomial(EquationPolynomial::constant(
                        numeric::literal(n, ty, c).map_err(invalid)?,
                        c,
                    )?))
                }
                ExprKind::Str(value) if path.is_empty() => Some(Binding::FiniteScalar(Scalar::Text(value.clone()))),
                ExprKind::Bool(value) if path.is_empty() => Some(Binding::Boolean(*value)),
                ExprKind::Unit if path.is_empty() => Some(Binding::FiniteScalar(Scalar::Unit)),
                ExprKind::ListLit { items, .. } if path.is_empty() => {
                    let Some(Type::List(element)) = self.inputs.law().expr_type(id) else { return Err(bad("原式のList型がない")) };
                    let mut bindings = Vec::new();
                    for item in items {
                        let Some(binding) = self.expression(*item, &[], c)? else { return Ok(None) };
                        bindings.push(binding);
                    }
                    Some(Binding::List { element: (**element).clone(), items: bindings })
                }
                ExprKind::SetLit { items, .. } if path.is_empty() => {
                    let Some(Type::Set(element)) = self.inputs.law().expr_type(id) else {
                        return Err(bad("原式のSet型がない"));
                    };
                    let mut values = Vec::new();
                    for item in items {
                        let Some(binding) = self.expression(*item, &[], c)? else {
                            return Ok(None);
                        };
                        let Some(value) = binding.finite_scalar(c)? else {
                            return Ok(None);
                        };
                        if value.ty() != **element {
                            return Ok(None);
                        }
                        values.push(value);
                    }
                    Some(Binding::FiniteScalar(super::super::data::set((**element).clone(), &values, c).map_err(invalid)?))
                }
                ExprKind::None(_) | ExprKind::Some(_) if path.is_empty() => {
                    let Some(Type::Option(element)) = self.inputs.law().expr_type(id) else { return Err(bad("原式のOption型がない")) };
                    let value = if let ExprKind::Some(inner) = expression.kind {
                        let Some(binding) = self.expression(inner, &[], c)? else { return Ok(None) };
                        Some(Box::new(binding))
                    } else { None };
                    Some(Binding::Option { element: (**element).clone(), value })
                }
                ExprKind::Unary { op: UnOp::Not, operand } if path.is_empty() => {
                    match self.expression(*operand, &[], c)? { Some(Binding::Boolean(value)) => Some(Binding::Boolean(!value)), _ => None }
                }
                ExprKind::Binary {
                    op: op @ (BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Eq | BinOp::Ne | BinOp::In | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge),
                    lhs,
                    rhs,
                } if path.is_empty() => {
                    let left = self.expression(*lhs, &[], c)?;
                    match (&left, op) {
                        (Some(Binding::Boolean(false)), BinOp::And) => return Ok(left),
                        (Some(Binding::Boolean(true)), BinOp::Or) => return Ok(left),
                        (Some(Binding::Boolean(false)), BinOp::Implies) => {
                            return Ok(Some(Binding::Boolean(true)));
                        }
                        _ => (),
                    }
                    let right = self.expression(*rhs, &[], c)?;
                    if matches!(op, BinOp::And | BinOp::Or | BinOp::Implies) {
                        let left = match &left { Some(value) => value.finite_scalar(c)?, None => None };
                        let right = match &right { Some(value) => value.finite_scalar(c)?, None => None };
                        return match super::super::environment::partial_binary(
                            *op, left.as_ref(), right.as_ref(), self.inputs.law(), expression.span, c,
                        ).map_err(invalid)? {
                            Some(Scalar::Bool(value)) => Ok(Some(Binding::Boolean(value))),
                            None => Ok(None),
                            _ => Err(bad("論理演算の結果がBoolでない")),
                        };
                    }
                    if let (Some(left), Some(right)) = (&left, &right)
                        && let (Some(left), Some(right)) =
                            (left.finite_scalar(c)?, right.finite_scalar(c)?)
                    {
                        let Scalar::Bool(value) = super::super::environment::binary(
                            *op,
                            &left,
                            &right,
                            self.inputs.law(),
                            expression.span,
                            c,
                        ).map_err(invalid)? else {
                            return Err(bad("有限述語の結果がBoolでない"));
                        };
                        return Ok(Some(Binding::Boolean(value)));
                    }
                    match (left, right) {
                        (Some(left), Some(right)) if matches!(op, BinOp::Eq | BinOp::Ne) => {
                            self.equal(&left, &right, expression.span, c)?.map(|value| Binding::Boolean(value == (*op == BinOp::Eq)))
                        }
                        (Some(left), Some(right)) if matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) => {
                            let Some(difference) = left.constant_difference(&right, c)? else { return Ok(None) };
                            let Some(value) = difference.evaluate(&[], c)? else { return Ok(None) };
                            let zero = numeric::zero(&difference.ty, c).map_err(invalid)?;
                            let Scalar::Bool(value) = numeric::binary(*op, value.scalar(), &zero, c).map_err(invalid)? else {
                                return Err(bad("順序比較の結果がBoolでない"));
                            };
                            Some(Binding::Boolean(value))
                        }
                        _ => None,
                    }
                }
                ExprKind::If { cond, then_branch, else_branch } => {
                    match self.expression(*cond, &[], c)? {
                        Some(Binding::Boolean(value)) => self.expression(if value { *then_branch } else { *else_branch }, path, c)?,
                        _ => None,
                    }
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
                    if let Binding::FiniteScalar(value) = value {
                        return Ok(Some(Binding::FiniteScalar(numeric::unary(UnOp::Neg, &value, c).map_err(invalid)?)));
                    }
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
                    let Some(body) = self.bind_match(id, *scrutinee, arms, c)? else {
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
                        && let [name] = names.as_slice()
                        && matches!(name.name.as_str(), "count" | "sum")
                    {
                        let [argument] = args.as_slice() else {
                            return Ok(None);
                        };
                        let Some(binding) = self.expression(*argument, &[], c)? else {
                            return Ok(None);
                        };
                        if name.name == "count" && let Binding::List { items, .. } = &binding {
                            let value = Scalar::Z(items.len().into());
                            return Ok(Some(if self.ring.ty == Type::Z {
                                Binding::Polynomial(EquationPolynomial::constant(value, c)?)
                            } else { Binding::FiniteScalar(value) }));
                        }
                        if name.name == "sum" && let Binding::List { element, items } = &binding
                            && element == &self.ring.ty
                        {
                            let mut total = Binding::Polynomial(EquationPolynomial::constant(numeric::zero(element, c).map_err(invalid)?, c)?);
                            for item in items {
                                tick(c)?;
                                let Some(next) = total.binary(BinOp::Add, item, c)? else { return Ok(None) };
                                total = next;
                            }
                            return Ok(Some(total));
                        }
                        let Some(value) = binding.finite_scalar(c)? else {
                            return Ok(None);
                        };
                        let value = super::super::data::aggregate(&name.name, &value, c).map_err(invalid)?;
                        return Ok(Some(if value.ty() == self.ring.ty {
                            Binding::Polynomial(EquationPolynomial::constant(value, c)?)
                        } else {
                            Binding::FiniteScalar(value)
                        }));
                    }
                    if let ExprKind::Dotted(names) = &self.inputs.law().exprs[callee].kind
                        && names.len() == 1
                        && names[0].name == "rat"
                    {
                        if !path.is_empty() || args.len() != 2 {
                            return Ok(None);
                        }
                        let numerator = self.integer_literal(args[0], c)?;
                        let denominator = self.integer_literal(args[1], c)?;
                        let value =
                            numeric::rational(&numerator, &denominator, c).map_err(invalid)?;
                        return Ok(Some(if self.ring.ty == Type::Q {
                            Binding::Polynomial(EquationPolynomial::constant(value, c)?)
                        } else {
                            Binding::FiniteScalar(value)
                        }));
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
    pub parameters: Vec<(affine::Parameter, EquationPolynomial)>,
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
            let term = coefficient.binary(BinOp::Mul, &EquationPolynomial::constant((*value).clone(), c)?, c)?;
            result = result.binary(BinOp::Add, &term, c)?;
        }
        Ok(result)
    }
    fn from_binding(value: &Binding, c: &mut Control) -> Result<Option<Self>, ConstructionFailure> {
        if let Binding::Family(family) = value { return Ok(Some(family.clone())); }
        let Some((polynomial, form)) = value.split(c)? else { return Ok(None) };
        let Some((constant, parameters)) = form.parameter_coordinates(c).map_err(invalid)? else { return Ok(None) };
        let parameters = parameters.into_iter().map(|(parameter, coefficient)| Ok((parameter, EquationPolynomial::constant(coefficient, c)?))).collect::<Result<_, ConstructionFailure>>()?;
        Ok(Some(Self { constant: polynomial.binary(BinOp::Add, &EquationPolynomial::constant(constant, c)?, c)?, parameters }))
    }
    fn binary(&self, op: BinOp, rhs: &Self, c: &mut Control) -> Result<Option<Self>, ConstructionFailure> {
        if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) { return Ok(None); }
        if op == BinOp::Mul && !self.parameters.is_empty() && !rhs.parameters.is_empty() { return Ok(None); }
        let constant = self.constant.binary(op, &rhs.constant, c)?;
        let mut parameters: Vec<(affine::Parameter, EquationPolynomial)> = vec![];
        let zero = EquationPolynomial::constant(numeric::zero(&constant.ty, c).map_err(invalid)?, c)?;
        for (family, factor, right) in [(self, &rhs.constant, false), (rhs, &self.constant, true)] {
            for (parameter, coefficient) in &family.parameters {
                tick(c)?;
                let coefficient = match op {
                    BinOp::Mul => coefficient.binary(BinOp::Mul, factor, c)?,
                    BinOp::Sub if right => zero.binary(BinOp::Sub, coefficient, c)?,
                    _ => coefficient.clone(),
                };
                if let Some((_, previous)) = parameters.iter_mut().find(|(p, _)| p == parameter) {
                    *previous = previous.binary(BinOp::Add, &coefficient, c)?;
                } else { parameters.push((parameter.clone(), coefficient)); }
            }
        }
        parameters.retain(|(_, coefficient)| !coefficient.terms.is_empty());
        parameters.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(Some(Self { constant, parameters }))
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
    family_operands_bound(inputs, instance, left, right, path, ring, &[], c)
}
pub(super) fn family_operands_bound(
    inputs: &CheckedInputs, instance: &ObjectInstance, left: usize, right: usize, path: &[usize],
    ring: &mut EquationRing, finite: &[(String, Scalar)], c: &mut Control,
) -> Result<Option<SourceFamilyDifference>, ConstructionFailure> {
    let Signature::Law { body, .. } = &inputs.law().declarations
        .get(&instance.declaration().name).ok_or_else(|| bad("原式のLaw宣言がない"))?.signature
    else { return Err(bad("原式の宣言がLawでない")) };
    family_operands_from_root(inputs, instance, *body, left, right, path, ring, finite, c)
}

#[cfg(test)]
pub(super) fn guard_value(inputs: &CheckedInputs, instance: &ObjectInstance, c: &mut Control) -> Result<Option<bool>, ConstructionFailure> {
    guard_value_bound(inputs, instance, &[], c)
}
pub(super) fn guard_value_bound(inputs: &CheckedInputs, instance: &ObjectInstance, finite: &[(String, Scalar)], c: &mut Control) -> Result<Option<bool>, ConstructionFailure> {
    let Signature::Law { guard, .. } = &inputs.law().declarations
        .get(&instance.declaration().name).ok_or_else(|| bad("元guardのLaw宣言がない"))?.signature
    else { return Ok(None) };
    let Some(root) = *guard else { return Ok(Some(true)) };
    let ty = instance.parameters().iter().find(|p| matches!(p.ty, Type::Z | Type::Q)).map(|p| p.ty.clone()).unwrap_or(Type::Z);
    let mut ring = EquationRing { ty, symbols: vec![], evaluation_images: Some(vec![]), required_generators: vec![] };
    let variables = variables_for(instance, finite, c)?;
    let mut compiler = Compiler { inputs, ring: &mut ring, variables };
    if let Some(Binding::Boolean(value)) = compiler.expression(root, &[], c)? { return Ok(Some(value)); }
    let mut cursor = root;
    let (left, right) = loop {
        tick(c)?;
        match inputs.law().exprs[cursor].kind {
            ExprKind::Group(next) => cursor = next,
            ExprKind::Call { .. } => {
                let Some((_, body, _)) = crate::observed::object_law_residuals::predicate_call(inputs,cursor) else { return Ok(None) };
                cursor = body;
            }
            ExprKind::Bool(value) => return Ok(Some(value)),
            ExprKind::Binary { op: BinOp::Eq, lhs, rhs } => break (lhs, rhs),
            _ => return Ok(None),
        }
    };
    let Some(ty @ (Type::Z | Type::Q)) = inputs.law().expr_type(left) else { return Ok(None) };
    let mut ring = EquationRing { ty: ty.clone(), symbols: vec![], evaluation_images: Some(vec![]), required_generators: vec![] };
    let Some(source) = family_operands_from_root(inputs, instance, root, left, right, &[], &mut ring, finite, c)? else { return Ok(None) };
    Ok((ring.symbols.is_empty() && source.difference.parameters.is_empty()).then_some(source.difference.constant.terms.is_empty()))
}

fn variables_for(
    instance: &ObjectInstance, finite: &[(String, Scalar)], c: &mut Control,
) -> Result<BTreeMap<String, Binding>, ConstructionFailure> {
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
    for (name, value) in finite {
        let binding = match value { Scalar::Bool(value) => Binding::Boolean(*value), _ => Binding::FiniteScalar(value.clone()) };
        variables.insert(name.clone(), binding);
    }
    Ok(variables)
}

fn family_operands_from_root(
    inputs: &CheckedInputs, instance: &ObjectInstance, root: usize,
    left: usize, right: usize, path: &[usize], ring: &mut EquationRing, finite: &[(String, Scalar)], c: &mut Control,
) -> Result<Option<SourceFamilyDifference>, ConstructionFailure> {
    let variables = variables_for(instance, finite, c)?;
    family_operands_from_variables(inputs, root, left, right, path, ring, variables, c)
}

/// 現在の束縛を使い、既存の原式正規化から全称数値引数の係数を得る。
pub(in crate::observed) fn parameter_differences_with_bindings(
    inputs: &CheckedInputs,
    root: usize,
    ty: &Type,
    context: crate::observed::call::Context,
    values: &[(String, Scalar)],
    parameters: &[(String, affine::Form)],
    c: &mut Control,
) -> Result<
    Option<(EquationRing, Vec<PolynomialFamily>, Vec<affine::Parameter>)>,
    ConstructionFailure,
> {
    if !matches!(ty, Type::Z | Type::Q) {
        return Ok(None);
    }
    let mut ring = EquationRing {
        ty: ty.clone(),
        symbols: vec![],
        evaluation_images: Some(vec![]),
        required_generators: vec![],
    };
    let mut variables = BTreeMap::new();
    for (name, value) in values {
        tick(c)?;
        let binding = match value {
            Scalar::Subject {
                snapshot, subject, ..
            } => Binding::Reference {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
            },
            Scalar::Bool(value) => Binding::Boolean(*value),
            value if value.ty() == *ty => {
                Binding::Polynomial(EquationPolynomial::constant(value.clone(), c)?)
            }
            value => Binding::FiniteScalar(value.clone()),
        };
        if variables.insert(name.clone(), binding).is_some() {
            return Err(bad("係数の束縛名が重複"));
        }
    }
    for (name, form) in parameters {
        tick(c)?;
        if variables
            .insert(name.clone(), Binding::ParameterForm(form.clone()))
            .is_some()
        {
            return Err(bad("係数の引数名が重複"));
        }
    }
    let mut compiler = Compiler {
        inputs,
        ring: &mut ring,
        variables,
    };
    let mut differences = vec![];
    let mut local_parameters = vec![];
    if collect_parameter_equations(
        &mut compiler,
        root,
        &mut differences,
        context,
        &mut local_parameters,
        c,
    )?
    .is_none()
    {
        return Ok(None);
    }
    Ok(Some((ring, differences, local_parameters)))
}
fn family_operands_from_variables(
    inputs: &CheckedInputs,
    root: usize,
    left: usize,
    right: usize,
    path: &[usize],
    ring: &mut EquationRing,
    variables: BTreeMap<String, Binding>,
    c: &mut Control,
) -> Result<Option<SourceFamilyDifference>, ConstructionFailure> {
    let mut candidate = ring.clone();
    let mut compiler = Compiler {
        inputs,
        ring: &mut candidate,
        variables,
    };
    if bind_root(&mut compiler, root, c)?.is_none() {
        return Ok(None);
    }
    let Some(result) = family_difference(&mut compiler, left, right, path, c)? else {
        return Ok(None);
    };
    *ring = candidate;
    Ok(Some(result))
}

// guardとbodyそれぞれの元rootからlexical束縛を復元し、互いのletを捕獲しない。
fn bind_root(
    compiler: &mut Compiler<'_>,
    root: usize,
    c: &mut Control,
) -> Result<Option<usize>, ConstructionFailure> {
    let mut cursor = root;
    loop {
        tick(c)?;
        match &compiler.inputs.law().exprs[cursor].kind {
            ExprKind::Group(child) => cursor = *child,
            ExprKind::Call { .. } => {
                let Some((params, body, args)) =
                    crate::observed::object_law_residuals::predicate_call(compiler.inputs, cursor)
                else {
                    return Ok(None);
                };
                let bindings = params
                    .iter()
                    .zip(args)
                    .map(|(p, a)| (p.name.clone(), compiler.lexical(*a)))
                    .collect();
                compiler.variables = bindings;
                cursor = body;
            }
            ExprKind::Let { name, value, body } => {
                let value = compiler.lexical(*value);
                compiler.variables.insert(name.name.clone(), value);
                cursor = *body;
            }
            ExprKind::Match { scrutinee, arms } => {
                let Some(body) = compiler.bind_match(cursor, *scrutinee, arms, c)? else {
                    return Ok(None);
                };
                cursor = body;
            }
            _ => return Ok(Some(cursor)),
        }
    }
}

fn collect_parameter_equations(
    compiler: &mut Compiler<'_>,
    root: usize,
    out: &mut Vec<PolynomialFamily>,
    context: crate::observed::call::Context,
    local_parameters: &mut Vec<affine::Parameter>,
    c: &mut Control,
) -> Result<Option<()>, ConstructionFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        let Some(cursor) = bind_root(compiler, root, c)? else {
            return Ok(None);
        };
        match &compiler.inputs.law().exprs[cursor].kind {
            ExprKind::Quant {
                kind: crate::law::ast::QuantKind::Forall,
                var,
                split:
                    crate::law::ast::QuantSplit::Fixed {
                        domain: crate::law::ast::QuantDomain::Type(_),
                        body,
                    },
            } => {
                let Some(ty) = compiler
                    .inputs
                    .law()
                    .quantifier_types
                    .get(cursor)
                    .and_then(Option::as_ref)
                else {
                    return Err(bad("全称係数の元binder型がない"));
                };
                let kind = match ty {
                    Type::Z => affine::NumberType::Z,
                    Type::Q => affine::NumberType::Q,
                    _ => return Ok(None),
                };
                if ty != &compiler.ring.ty {
                    return Ok(None);
                }
                let parameter = affine::Parameter {
                    binder: var.span,
                    name: var.name.clone(),
                    context,
                    kind,
                };
                let Some(form) = affine::parameter(ty, &parameter, c).map_err(invalid)? else {
                    return Ok(None);
                };
                let previous = compiler.variables.clone();
                compiler
                    .variables
                    .insert(var.name.clone(), Binding::ParameterForm(form));
                local_parameters.push(parameter);
                let result =
                    collect_parameter_equations(compiler, *body, out, context, local_parameters, c);
                compiler.variables = previous;
                result
            }
            ExprKind::Binary {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                let previous = compiler.variables.clone();
                if collect_parameter_equations(compiler, *lhs, out, context, local_parameters, c)?
                    .is_none()
                {
                    return Ok(None);
                }
                compiler.variables = previous.clone();
                let result =
                    collect_parameter_equations(compiler, *rhs, out, context, local_parameters, c);
                compiler.variables = previous;
                result
            }
            ExprKind::Binary {
                op: BinOp::Eq,
                lhs,
                rhs,
            } if compiler.inputs.law().expr_type(*lhs) == Some(&compiler.ring.ty) => {
                let Some(source) = family_difference(compiler, *lhs, *rhs, &[], c)? else {
                    return Ok(None);
                };
                out.push(source.difference);
                Ok(Some(()))
            }
            _ => match compiler.expression(cursor, &[], c)? {
                Some(Binding::Boolean(value)) => {
                    if !value {
                        let one = numeric::literal("1", &compiler.ring.ty, c).map_err(invalid)?;
                        out.push(PolynomialFamily {
                            constant: EquationPolynomial::constant(one, c)?,
                            parameters: vec![],
                        });
                    }
                    Ok(Some(()))
                }
                _ => Ok(None),
            },
        }
    })
}

fn family_difference(
    compiler: &mut Compiler<'_>,
    left: usize,
    right: usize,
    path: &[usize],
    c: &mut Control,
) -> Result<Option<SourceFamilyDifference>, ConstructionFailure> {
    let Some(left) = compiler.expression(left, path, c)? else {
        return Ok(None);
    };
    let Some(right) = compiler.expression(right, path, c)? else {
        return Ok(None);
    };
    let Some(difference) = left.binary(BinOp::Sub, &right, c)? else {
        return Ok(None);
    };
    let (Some(left), Some(right), Some(difference)) = (
        PolynomialFamily::from_binding(&left, c)?,
        PolynomialFamily::from_binding(&right, c)?,
        PolynomialFamily::from_binding(&difference, c)?,
    ) else {
        return Ok(None);
    };
    Ok(Some(SourceFamilyDifference {
        left,
        right,
        difference,
    }))
}
