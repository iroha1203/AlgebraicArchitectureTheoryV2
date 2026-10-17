//! 元Termの型付きbodyへ、引数の位置または観測の相関する数値式を代入する。
use super::*;
use crate::law::ast::UnOp;
use crate::observed::result::Fact;
use crate::observed::{affine as forms, finite, value_equality};

#[derive(Debug)]
pub(in crate::observed) enum Value {
    Known(Scalar),
    Number(forms::Form),
    Tuple(Vec<Value>),
    List { element: Type, items: Vec<Value> },
    Unsupported(Type),
}
impl Clone for Value {
    fn clone(&self) -> Self {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
            Self::Known(v) => Self::Known(v.clone()),
            Self::Number(v) => Self::Number(v.clone()),
            Self::Tuple(v) => Self::Tuple(v.clone()),
            Self::List { element, items } => Self::List {
                element: element.clone(),
                items: items.clone(),
            },
            Self::Unsupported(t) => Self::Unsupported(t.clone()),
        })
    }
}
impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match (self, other) {
            (Self::Known(a), Self::Known(b)) => a == b,
            (Self::Number(a), Self::Number(b)) => a == b,
            (Self::Tuple(a), Self::Tuple(b)) => a == b,
            (
                Self::List {
                    element: a,
                    items: x,
                },
                Self::List {
                    element: b,
                    items: y,
                },
            ) => a == b && x == y,
            (Self::Unsupported(a), Self::Unsupported(b)) => a == b,
            _ => false,
        })
    }
}
impl Eq for Value {}
impl Drop for Value {
    fn drop(&mut self) {
        let mut pending = match self {
            Self::Tuple(v) | Self::List { items: v, .. } => std::mem::take(v),
            _ => return,
        };
        while let Some(mut value) = pending.pop() {
            match &mut value {
                Self::Tuple(v) | Self::List { items: v, .. } => pending.append(v),
                _ => {}
            }
        }
    }
}
impl Value {
    pub(in crate::observed) fn missing(
        ty: &Type,
        fact: &Fact,
        path: &[usize],
        c: &Control,
    ) -> Result<Self, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            if let Some(form) = forms::missing_component(ty, fact, path, c)? {
                return Ok(Self::Number(form));
            }
            Ok(match ty {
                Type::Tuple(types) => Self::Tuple(
                    types
                        .iter()
                        .enumerate()
                        .map(|(i, t)| {
                            let mut p = path.to_vec();
                            p.push(i);
                            Self::missing(t, fact, &p, c)
                        })
                        .collect::<Result<_, _>>()?,
                ),
                _ => Self::Unsupported(ty.clone()),
            })
        })
    }
    pub(in crate::observed) fn unsupported(&self, c: &Control) -> Result<bool, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            match self {
                Self::Unsupported(_) => Ok(true),
                Self::Tuple(v) | Self::List { items: v, .. } => {
                    for v in v {
                        if v.unsupported(c)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                _ => Ok(false),
            }
        })
    }
    pub(in crate::observed) fn ty(&self, c: &Control) -> Result<Type, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            Ok(match self {
                Self::Known(v) => v.ty(),
                Self::Number(v) => v.ty(c)?,
                Self::Tuple(v) => Type::Tuple(v.iter().map(|x| x.ty(c)).collect::<Result<_, _>>()?),
                Self::List { element, .. } => Type::List(Box::new(element.clone())),
                Self::Unsupported(t) => t.clone(),
            })
        })
    }
    pub(in crate::observed) fn known(
        &self,
        c: &Control,
    ) -> Result<Option<Scalar>, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            match self {
                Self::Known(v) => Ok(Some(v.clone())),
                Self::Number(v) => v.value(c),
                Self::Tuple(v) => {
                    let mut values = Vec::new();
                    for x in v {
                        let Some(x) = x.known(c)? else {
                            return Ok(None);
                        };
                        values.push(x);
                    }
                    Ok(Some(Scalar::Tuple(values)))
                }
                Self::List { element, items } => {
                    let mut values = Vec::new();
                    for v in items {
                        let Some(v) = v.known(c)? else {
                            return Ok(None);
                        };
                        values.push(v);
                    }
                    Ok(Some(Scalar::List {
                        element: element.clone(),
                        items: values,
                    }))
                }
                Self::Unsupported(_) => Ok(None),
            }
        })
    }
    pub(in crate::observed) fn number(
        &self,
        c: &Control,
    ) -> Result<Option<forms::Form>, ValidationFailure> {
        tick(c)?;
        match self {
            Self::Known(v) => forms::constant(v, c),
            Self::Number(f) => Ok(Some(f.clone())),
            _ => Ok(None),
        }
    }
    fn at(
        &self,
        unit: Option<&forms::TermArgument>,
        c: &Control,
    ) -> Result<Scalar, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            match self {
                Self::Known(v) => Ok(v.clone()),
                Self::Number(f) => forms::term_point(f, unit, c),
                Self::Tuple(v) => Ok(Scalar::Tuple(
                    v.iter().map(|x| x.at(unit, c)).collect::<Result<_, _>>()?,
                )),
                Self::List { element, items } => Ok(Scalar::List {
                    element: element.clone(),
                    items: items
                        .iter()
                        .map(|x| x.at(unit, c))
                        .collect::<Result<_, _>>()?,
                }),
                Self::Unsupported(_) => Err("未対応値をTerm反例点にできない".into()),
            }
        })
    }
}
fn list_values(v: &Value, c: &Control) -> Result<Option<Vec<Value>>, ValidationFailure> {
    tick(c)?;
    Ok(match v {
        Value::List { items, .. } => Some(items.clone()),
        Value::Known(Scalar::List { items, .. }) => {
            Some(items.iter().cloned().map(Value::Known).collect())
        }
        _ => None,
    })
}
fn tuple_values(v: &Value, c: &Control) -> Result<Option<Vec<Value>>, ValidationFailure> {
    tick(c)?;
    Ok(match v {
        Value::Tuple(v) => Some(v.clone()),
        Value::Known(Scalar::Tuple(v)) => Some(v.iter().cloned().map(Value::Known).collect()),
        _ => None,
    })
}
pub(in crate::observed) fn pointwise_equal(
    a: &Value,
    b: &Value,
    law: &CheckedLaw,
    c: &Control,
) -> Result<Option<bool>, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        if a.ty(c)? != b.ty(c)? {
            return Err("Term記号等値の左右型が違う".into());
        }
        if let (Some(a), Some(b)) = (a.known(c)?, b.known(c)?) {
            return value_equality::equal(&a, &b, law, c);
        }
        if let (Some(a), Some(b)) = (tuple_values(a, c)?, tuple_values(b, c)?) {
            let mut known = true;
            for (a, b) in a.iter().zip(&b) {
                match pointwise_equal(a, b, law, c)? {
                    Some(false) => return Ok(Some(false)),
                    None => known = false,
                    _ => {}
                }
            }
            return Ok(known.then_some(true));
        }
        Ok(
            forms::equality(BinOp::Eq, a.number(c)?.as_ref(), b.number(c)?.as_ref(), c)?.and_then(
                |(v, _)| match v {
                    Scalar::Bool(v) => Some(v),
                    _ => None,
                },
            ),
        )
    })
}
pub(in crate::observed) fn operation(
    op: BinOp,
    a: &Value,
    b: &Value,
    ty: &Type,
    law: &CheckedLaw,
    span: Span,
    c: &Control,
) -> Result<Value, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        if let (Some(a), Some(b)) = (a.known(c)?, b.known(c)?) {
            return Ok(
                environment::partial_binary(op, Some(&a), Some(&b), law, span, c)?
                    .map(Value::Known)
                    .unwrap_or_else(|| Value::Unsupported(ty.clone())),
            );
        }
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            return Ok(pointwise_equal(a, b, law, c)?
                .map(|v| Value::Known(Scalar::Bool(if op == BinOp::Eq { v } else { !v })))
                .unwrap_or_else(|| Value::Unsupported(ty.clone())));
        }
        if let (Some(a), Some(b)) = (tuple_values(a, c)?, tuple_values(b, c)?) {
            if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
                if a.len() != b.len() {
                    return Err("Term記号演算のTuple長が違う".into());
                }
                let mut values = Vec::new();
                for (a, b) in a.iter().zip(&b) {
                    values.push(operation(op, a, b, &a.ty(c)?, law, span, c)?);
                }
                return Ok(Value::Tuple(values));
            }
        }
        if environment::is_boolean_binary(op) {
            return Ok(environment::partial_binary(
                op,
                a.known(c)?.as_ref(),
                b.known(c)?.as_ref(),
                law,
                span,
                c,
            )?
            .map(Value::Known)
            .unwrap_or_else(|| Value::Unsupported(ty.clone())));
        }
        Ok(
            forms::binary(op, a.number(c)?.as_ref(), b.number(c)?.as_ref(), c)?
                .map(Value::Number)
                .unwrap_or_else(|| Value::Unsupported(ty.clone())),
        )
    })
}
fn domain(
    t: &Type,
    argument: usize,
    path: &[usize],
    law: &CheckedLaw,
    c: &Control,
) -> Result<Option<Vec<Value>>, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        match t {
            Type::Z | Type::Q => Ok(Some(vec![Value::Number(forms::term_argument(
                forms::TermArgument {
                    argument,
                    component: path.to_vec(),
                    kind: if *t == Type::Z {
                        forms::NumberType::Z
                    } else {
                        forms::NumberType::Q
                    },
                },
                c,
            )?)])),
            Type::Tuple(items) => {
                let mut rows = vec![Vec::new()];
                for (i, t) in items.iter().enumerate() {
                    let mut p = path.to_vec();
                    p.push(i);
                    let Some(values) = domain(t, argument, &p, law, c)? else {
                        return Ok(None);
                    };
                    let mut next = Vec::new();
                    for row in &rows {
                        for value in &values {
                            tick(c)?;
                            let mut row = row.clone();
                            row.push(value.clone());
                            next.push(row);
                            tick(c)?;
                        }
                    }
                    rows = next;
                }
                Ok(Some(rows.into_iter().map(Value::Tuple).collect()))
            }
            _ if finite::completion_supported(t, law, c)? => Ok(Some(
                finite::values(
                    t,
                    law,
                    c,
                    &mut |_| Err("Term引数に参照族を置けない".into()),
                    &mut |_| {},
                )?
                .values
                .into_iter()
                .map(Value::Known)
                .collect(),
            )),
            _ => Ok(None),
        }
    })
}
enum Comparison {
    Same,
    Different(Option<forms::TermArgument>),
    Unsupported,
}
fn compare(
    a: &Value,
    b: &Value,
    law: &CheckedLaw,
    c: &Control,
) -> Result<Comparison, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        if a.ty(c)? != b.ty(c)? {
            return Err("Term正規形の左右型が違う".into());
        }
        if let (Some(a), Some(b)) = (a.number(c)?, b.number(c)?) {
            return Ok(match forms::term_difference(&a, &b, c)? {
                forms::TermDifference::Same => Comparison::Same,
                forms::TermDifference::Different { unit } => Comparison::Different(unit),
            });
        }
        if let (Some(a), Some(b)) = (list_values(a, c)?, list_values(b, c)?) {
            if a.len() != b.len() {
                return Ok(Comparison::Different(None));
            }
            let mut unknown = false;
            for (a, b) in a.iter().zip(&b) {
                match compare(a, b, law, c)? {
                    Comparison::Same => {}
                    Comparison::Unsupported => unknown = true,
                    d => return Ok(d),
                }
            }
            return Ok(if unknown {
                Comparison::Unsupported
            } else {
                Comparison::Same
            });
        }
        if let (Some(a), Some(b)) = (tuple_values(a, c)?, tuple_values(b, c)?) {
            if a.len() != b.len() {
                return Err("Term正規形のTuple長が違う".into());
            }
            let mut unknown = false;
            for (a, b) in a.iter().zip(&b) {
                match compare(a, b, law, c)? {
                    Comparison::Same => {}
                    Comparison::Unsupported => unknown = true,
                    d => return Ok(d),
                }
            }
            return Ok(if unknown {
                Comparison::Unsupported
            } else {
                Comparison::Same
            });
        }
        Ok(match a.known(c)?.zip(b.known(c)?) {
            Some((a, b)) => match value_equality::equal(&a, &b, law, c)? {
                Some(true) => Comparison::Same,
                Some(false) => Comparison::Different(None),
                None => Comparison::Unsupported,
            },
            None => Comparison::Unsupported,
        })
    })
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Case {
    pub arguments: Vec<Value>,
    pub left: Value,
    pub right: Value,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Point {
    pub arguments: Vec<Scalar>,
    pub left: Scalar,
    pub right: Scalar,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Certificate {
    pub(in crate::observed) cases: Vec<Case>,
    pub(in crate::observed) point: Option<Point>,
}
impl Certificate {
    pub(in crate::observed) fn equal(&self) -> bool {
        self.point.is_none()
    }
    pub(in crate::observed) fn identical(
        &self,
        other: &Self,
        c: &Control,
    ) -> Result<bool, ValidationFailure> {
        tick(c)?;
        if self.cases.len() != other.cases.len() || self.point != other.point {
            return Ok(false);
        }
        for (a, b) in self.cases.iter().zip(&other.cases) {
            tick(c)?;
            if a.arguments.len() != b.arguments.len()
                || !a.left.identical(&b.left, c)?
                || !a.right.identical(&b.right, c)?
            {
                return Ok(false);
            }
            for (a, b) in a.arguments.iter().zip(&b.arguments) {
                if !a.identical(b, c)? {
                    return Ok(false);
                }
            }
        }
        tick(c)?;
        Ok(true)
    }
}
impl Value {
    fn normal_form(&self, c: &Control) -> Result<Self, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            let value = match self {
                Self::Known(v) => {
                    if let Some(form) = forms::constant(v, c)? {
                        Self::Number(form)
                    } else {
                        match v {
                            Scalar::Tuple(items) => Self::Tuple(
                                items
                                    .iter()
                                    .map(|v| Self::Known(v.clone()).normal_form(c))
                                    .collect::<Result<_, _>>()?,
                            ),
                            Scalar::List { element, items } => Self::List {
                                element: element.clone(),
                                items: items
                                    .iter()
                                    .map(|v| Self::Known(v.clone()).normal_form(c))
                                    .collect::<Result<_, _>>()?,
                            },
                            _ => self.clone(),
                        }
                    }
                }
                Self::Tuple(items) => Self::Tuple(
                    items
                        .iter()
                        .map(|v| v.normal_form(c))
                        .collect::<Result<_, _>>()?,
                ),
                Self::List { element, items } => Self::List {
                    element: element.clone(),
                    items: items
                        .iter()
                        .map(|v| v.normal_form(c))
                        .collect::<Result<_, _>>()?,
                },
                _ => self.clone(),
            };
            tick(c)?;
            Ok(value)
        })
    }
    pub(in crate::observed) fn identical(
        &self,
        other: &Self,
        c: &Control,
    ) -> Result<bool, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            let same = match (self, other) {
                (Self::Tuple(a), Self::Tuple(b))
                | (Self::List { items: a, .. }, Self::List { items: b, .. }) => {
                    if self.ty(c)? != other.ty(c)? || a.len() != b.len() {
                        return Ok(false);
                    }
                    for (a, b) in a.iter().zip(b) {
                        if !a.identical(b, c)? {
                            return Ok(false);
                        }
                    }
                    true
                }
                _ => self == other,
            };
            tick(c)?;
            Ok(same)
        })
    }
}
pub(in crate::observed) fn equal(
    a: &Term,
    b: &Term,
    law: &CheckedLaw,
    c: &Control,
) -> Result<Option<bool>, ValidationFailure> {
    Ok(comparison(a, b, law, c)?.map(|v| v.equal()))
}
pub(in crate::observed) fn comparison(
    a: &Term,
    b: &Term,
    law: &CheckedLaw,
    c: &Control,
) -> Result<Option<Certificate>, ValidationFailure> {
    a.check(c)?;
    b.check(c)?;
    if a.ty() != b.ty() {
        return Err("アフィンTermの左右型が違う".into());
    }
    let mut rows = vec![Vec::new()];
    for (i, (_, t)) in a.params.iter().enumerate() {
        let Some(values) = domain(t, i, &[], law, c)? else {
            return Ok(None);
        };
        let mut next = Vec::new();
        for row in &rows {
            for v in &values {
                tick(c)?;
                let mut row = row.clone();
                row.push(v.clone());
                next.push(row);
                tick(c)?;
            }
        }
        rows = next;
    }
    let mut cases = Vec::new();
    for (_index, row) in rows.iter().enumerate() {
        #[cfg(test)]
        data::observe_iteration("term_affine_case", _index);
        tick(c)?;
        let left = a.apply_symbolic(row, law, c)?.normal_form(c)?;
        let right = b.apply_symbolic(row, law, c)?.normal_form(c)?;
        // 証拠へ保持する全成分を係数化できるcaseだけを受理する。
        // 部分的な相違だけで算法外成分を正規形表示へ持ち込まない。
        if left.unsupported(c)? || right.unsupported(c)? {
            return Ok(None);
        }
        let result = compare(&left, &right, law, c)?;
        cases.push(Case {
            arguments: row.clone(),
            left,
            right,
        });
        match result {
            Comparison::Same => {}
            Comparison::Unsupported => return Ok(None),
            Comparison::Different(unit) => {
                let args = row
                    .iter()
                    .map(|v| v.at(unit.as_ref(), c))
                    .collect::<Result<Vec<_>, _>>()?;
                let (left, right) = (a.apply(&args, law, c)?, b.apply(&args, law, c)?);
                if value_equality::equal(&left, &right, law, c)? != Some(false) {
                    return Err("Term係数の反例が元bodyへの再代入で相違しない".into());
                }
                return Ok(Some(Certificate {
                    cases,
                    point: Some(Point {
                        arguments: args,
                        left,
                        right,
                    }),
                }));
            }
        }
        tick(c)?;
    }
    Ok(Some(Certificate { cases, point: None }))
}
impl Term {
    pub(in crate::observed) fn apply_symbolic(
        &self,
        args: &[Value],
        law: &CheckedLaw,
        c: &Control,
    ) -> Result<Value, ValidationFailure> {
        self.check(c)?;
        if args.len() != self.params.len() {
            return Err("Term記号適用の元引数数が違う".into());
        }
        let mut vars = BTreeMap::new();
        let mut known = Vec::new();
        let mut all_known = true;
        for ((name, t), v) in self.params.iter().zip(args) {
            tick(c)?;
            if *t != v.ty(c)? {
                return Err("Term記号適用の元引数型が違う".into());
            }
            if let Some(v) = v.known(c)? {
                known.push(v)
            } else {
                all_known = false
            }
            vars.insert(name.clone(), v.clone());
        }
        if all_known {
            return Ok(Value::Known(self.apply(&known, law, c)?));
        }
        let value = self.symbolic(self.root, &vars, law, c)?;
        if value.ty(c)? != self.returns {
            return Err("Term記号適用の元戻り型が違う".into());
        }
        Ok(value)
    }
    fn symbolic(
        &self,
        id: usize,
        vars: &BTreeMap<String, Value>,
        law: &CheckedLaw,
        c: &Control,
    ) -> Result<Value, ValidationFailure> {
        stacker::maybe_grow(128 * 1024, 1024 * 1024, || {
            tick(c)?;
            let e = self.nodes.get(&id).ok_or("Term記号計算の元式がない")?;
            let ty = self.types.get(&id).ok_or("Term記号計算の元型がない")?;
            let unknown = || Value::Unsupported(ty.clone());
            let value = match &e.kind {
                ExprKind::Int(n) => Value::Known(numeric::literal(n, ty, c)?),
                ExprKind::Bool(v) => Value::Known(Scalar::Bool(*v)),
                ExprKind::Str(v) => Value::Known(Scalar::Text(v.clone())),
                ExprKind::Unit => Value::Known(Scalar::Unit),
                ExprKind::Dotted(parts)
                    if parts.len() == 1 && vars.contains_key(&parts[0].name) =>
                {
                    vars[&parts[0].name].clone()
                }
                ExprKind::Group(i) => self.symbolic(*i, vars, law, c)?,
                ExprKind::Let { name, value, body } => {
                    let v = self.symbolic(*value, vars, law, c)?;
                    let mut local = BTreeMap::new();
                    for (n, v) in vars {
                        tick(c)?;
                        local.insert(n.clone(), v.clone());
                    }
                    if local.insert(name.name.clone(), v).is_some() {
                        return Err("Term記号let束縛が重複する".into());
                    }
                    self.symbolic(*body, &local, law, c)?
                }
                ExprKind::Tuple(items) => Value::Tuple(
                    items
                        .iter()
                        .map(|i| self.symbolic(*i, vars, law, c))
                        .collect::<Result<_, _>>()?,
                ),
                ExprKind::ListLit { items, .. } => {
                    let Type::List(element) = ty else {
                        return Err("Term記号Listの元型が違う".into());
                    };
                    Value::List {
                        element: (**element).clone(),
                        items: items
                            .iter()
                            .map(|i| self.symbolic(*i, vars, law, c))
                            .collect::<Result<_, _>>()?,
                    }
                }
                ExprKind::Index { base, index, .. } => match self.symbolic(*base, vars, law, c)? {
                    Value::Tuple(ref v) => v.get(*index).ok_or("Term記号Tuple位置が違う")?.clone(),
                    Value::Known(Scalar::Tuple(ref v)) => {
                        Value::Known(v.get(*index).ok_or("Term既知Tuple位置が違う")?.clone())
                    }
                    _ => unknown(),
                },
                ExprKind::Unary { op, operand } => {
                    let a = self.symbolic(*operand, vars, law, c)?;
                    if let Some(a) = a.known(c)? {
                        Value::Known(environment::unary(*op, &a, c)?)
                    } else if *op == UnOp::Neg && tuple_values(&a, c)?.is_some() {
                        let zero = Value::Known(numeric::zero(ty, c)?);
                        operation(BinOp::Sub, &zero, &a, ty, law, e.span, c)?
                    } else if let Some(f) = forms::unary(*op, a.number(c)?.as_ref(), c)? {
                        Value::Number(f)
                    } else {
                        unknown()
                    }
                }
                ExprKind::Binary { op, lhs, rhs } => {
                    let a = self.symbolic(*lhs, vars, law, c)?;
                    let short = match (op, a.known(c)?) {
                        (BinOp::And, Some(Scalar::Bool(false))) => Some(false),
                        (BinOp::Or, Some(Scalar::Bool(true)))
                        | (BinOp::Implies, Some(Scalar::Bool(false))) => Some(true),
                        _ => None,
                    };
                    if let Some(v) = short {
                        Value::Known(Scalar::Bool(v))
                    } else {
                        let b = self.symbolic(*rhs, vars, law, c)?;
                        operation(*op, &a, &b, ty, law, e.span, c)?
                    }
                }
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => match self.symbolic(*cond, vars, law, c)?.known(c)? {
                    Some(Scalar::Bool(true)) => self.symbolic(*then_branch, vars, law, c)?,
                    Some(Scalar::Bool(false)) => self.symbolic(*else_branch, vars, law, c)?,
                    None => {
                        let a = self.symbolic(*then_branch, vars, law, c)?;
                        let b = self.symbolic(*else_branch, vars, law, c)?;
                        let same = pointwise_equal(&a, &b, law, c)? == Some(true);
                        if same { a } else { unknown() }
                    }
                    _ => return Err("Term記号if条件がBoolでない".into()),
                },
                ExprKind::Match { scrutinee, arms } => {
                    if let Some(v) = self.symbolic(*scrutinee, vars, law, c)?.known(c)? {
                        let mut answer = None;
                        for arm in arms {
                            tick(c)?;
                            let mut bound = BTreeMap::new();
                            if self.pattern(&arm.pattern, &v, &mut bound, c)? {
                                let mut local = vars.clone();
                                for (n, v) in bound {
                                    tick(c)?;
                                    local.insert(n, Value::Known(v));
                                }
                                answer = Some(self.symbolic(arm.body, &local, law, c)?);
                                break;
                            }
                        }
                        answer.ok_or("Term記号matchの元選択枝がない")?
                    } else {
                        unknown()
                    }
                }
                ExprKind::Quant {
                    kind,
                    var,
                    split: QuantSplit::Fixed { domain, body },
                } => {
                    let element = self
                        .quantifier_types
                        .get(&id)
                        .ok_or("Term記号量化の元binder型がない")?;
                    let values = match domain {
                        QuantDomain::In(i) => self
                            .symbolic(*i, vars, law, c)?
                            .known(c)?
                            .map(|v| match &v {
                                Scalar::List { items, .. } | Scalar::Set { items, .. } => {
                                    Ok(items.clone())
                                }
                                _ => Err(ValidationFailure::from(
                                    "Term記号量化域が有限containerでない",
                                )),
                            })
                            .transpose()?,
                        QuantDomain::Type(_) => {
                            if finite::completion_supported(element, law, c)? {
                                Some(
                                    finite::values(
                                        element,
                                        law,
                                        c,
                                        &mut |_| Err("Term量化に参照族を置けない".into()),
                                        &mut |_| {},
                                    )?
                                    .values,
                                )
                            } else {
                                None
                            }
                        }
                    };
                    if let Some(values) = values {
                        let mut result = Some(*kind == QuantKind::Forall);
                        for v in values {
                            tick(c)?;
                            let mut local = BTreeMap::new();
                            for (n, v) in vars {
                                tick(c)?;
                                local.insert(n.clone(), v.clone());
                            }
                            if local.insert(var.name.clone(), Value::Known(v)).is_some() {
                                return Err("Term記号量化束縛が重複する".into());
                            }
                            match self.symbolic(*body, &local, law, c)?.known(c)? {
                                Some(Scalar::Bool(b)) => {
                                    if (*kind == QuantKind::Forall && !b)
                                        || (*kind == QuantKind::Exists && b)
                                    {
                                        result = Some(b);
                                        break;
                                    }
                                }
                                None => result = None,
                                _ => return Err("Term記号量化bodyがBoolでない".into()),
                            }
                        }
                        result
                            .map(|b| Value::Known(Scalar::Bool(b)))
                            .unwrap_or_else(unknown)
                    } else {
                        unknown()
                    }
                }
                ExprKind::Call { callee, args } => {
                    let a = args
                        .iter()
                        .map(|i| self.symbolic(*i, vars, law, c))
                        .collect::<Result<Vec<_>, _>>()?;
                    // Term bodyの組込みとconstructorの既知引数計算は元の実評価を再利用する。
                    let mut target = *callee;
                    while let ExprKind::Group(inner) =
                        &self.nodes.get(&target).ok_or("Term元calleeがない")?.kind
                    {
                        tick(c)?;
                        target = *inner;
                    }
                    let builtin_name = match &self.nodes[&target].kind {
                        ExprKind::Dotted(parts) if parts.len() == 1 => Some(parts[0].name.as_str()),
                        _ => None,
                    };
                    let builtin = matches!(builtin_name, Some("rat" | "count" | "sum"));
                    if !builtin && matches!(self.types.get(callee), Some(Type::Term(..))) {
                        match self.symbolic(*callee, vars, law, c)?.known(c)? {
                            Some(Scalar::Term(ref t)) => t.apply_symbolic(&a, law, c)?,
                            _ => unknown(),
                        }
                    } else if matches!(builtin_name, Some("sum" | "count"))
                        && a.len() == 1
                        && matches!(a[0], Value::List { .. })
                    {
                        let Value::List { element, items } = &a[0] else {
                            unreachable!()
                        };
                        if builtin_name == Some("count") {
                            Value::Known(numeric::literal(&items.len().to_string(), &Type::Z, c)?)
                        } else {
                            let mut total = Value::Known(numeric::zero(element, c)?);
                            for item in items {
                                tick(c)?;
                                total =
                                    operation(BinOp::Add, &total, item, element, law, e.span, c)?;
                            }
                            total
                        }
                    } else if a
                        .iter()
                        .map(|v| v.known(c))
                        .collect::<Result<Vec<_>, _>>()?
                        .iter()
                        .all(Option::is_some)
                    {
                        // 一般evalへ未知変数の名前を渡さず、実引数の式ではなく既知化済み値を使う。
                        self.symbolic_known_call(id, &a, law, c)?
                    } else {
                        unknown()
                    }
                }
                _ => {
                    let mut concrete = BTreeMap::new();
                    let mut all = true;
                    for (n, v) in vars {
                        tick(c)?;
                        if let Some(v) = v.known(c)? {
                            concrete.insert(n.clone(), v);
                        } else {
                            all = false
                        }
                    }
                    if all
                        || matches!(
                            e.kind,
                            ExprKind::Fn { .. } | ExprKind::None(_) | ExprKind::Dotted(_)
                        )
                    {
                        Value::Known(self.eval(id, &concrete, law, c)?)
                    } else {
                        unknown()
                    }
                }
            };
            if value.ty(c)? != *ty {
                return Err("Term記号部分式の元型が違う".into());
            }
            tick(c)?;
            Ok(value)
        })
    }
    fn symbolic_known_call(
        &self,
        id: usize,
        args: &[Value],
        law: &CheckedLaw,
        c: &Control,
    ) -> Result<Value, ValidationFailure> {
        let ExprKind::Call { callee, .. } = &self.nodes.get(&id).ok_or("Term元callがない")?.kind
        else {
            return Err("Term元call形が違う".into());
        };
        let mut callee = *callee;
        while let ExprKind::Group(inner) =
            &self.nodes.get(&callee).ok_or("Term元call先がない")?.kind
        {
            tick(c)?;
            callee = *inner;
        }
        let values = args
            .iter()
            .map(|v| {
                v.known(c)?
                    .ok_or_else(|| ValidationFailure::from("Term既知callに未知引数がある"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ExprKind::Dotted(parts) = &self.nodes[&callee].kind else {
            return Err("Term組込みcallee形が違う".into());
        };
        let name = parts
            .iter()
            .map(|p| p.name.as_str())
            .collect::<Vec<_>>()
            .join(".");
        let ty = &self.types[&id];
        let value = match name.as_str() {
            "rat" => {
                if values.len() != 2 {
                    return Err("Term rat引数数が違う".into());
                }
                numeric::rational(&values[0], &values[1], c)?
            }
            "count" | "sum" if values.len() == 1 => data::aggregate(&name, &values[0], c)?,
            _ => {
                let Type::Data(family) = ty else {
                    return Ok(Value::Unsupported(ty.clone()));
                };
                let reference = self
                    .reference(self.nodes[&callee].span, c)?
                    .ok_or("Term constructor参照がない")?;
                let ctor = data::constructor(law, family, reference, c)?;
                if ctor.arguments.len() != values.len() {
                    return Err("Term constructor引数数が違う".into());
                }
                Scalar::Data {
                    family: family.clone(),
                    constructor: reference.into(),
                    args: values,
                }
            }
        };
        Ok(Value::Known(value))
    }
}

/// 正規形は既存ScalarのList/Tupleとして表示する。各rowは元引数の零点と
/// 出力の(定数項,全係数)であり、軸順は元parameter順・Tuple成分順で固定する。
impl Certificate {
    pub(in crate::observed) fn presentation(
        &self,
        term: &Term,
        left: bool,
        c: &Control,
    ) -> Result<Scalar, ValidationFailure> {
        fn axes(
            ty: &Type,
            argument: usize,
            path: &mut Vec<usize>,
            out: &mut Vec<forms::TermArgument>,
            c: &Control,
        ) -> Result<(), ValidationFailure> {
            stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
                tick(c)?;
                match ty {
                    Type::Z | Type::Q => out.push(forms::TermArgument {
                        argument,
                        component: path.clone(),
                        kind: if *ty == Type::Z {
                            forms::NumberType::Z
                        } else {
                            forms::NumberType::Q
                        },
                    }),
                    Type::Tuple(ts) => {
                        for (i, t) in ts.iter().enumerate() {
                            path.push(i);
                            axes(t, argument, path, out, c)?;
                            path.pop();
                        }
                    }
                    _ => {}
                }
                Ok(())
            })
        }
        let mut coordinates = vec![];
        for (i, (_, ty)) in term.params.iter().enumerate() {
            axes(ty, i, &mut vec![], &mut coordinates, c)?;
        }
        let pack = |values: Vec<Scalar>| match values.len() {
            0 => Scalar::Unit,
            1 => values.into_iter().next().unwrap(),
            _ => Scalar::Tuple(values),
        };
        let mut rows = vec![];
        for case in &self.cases {
            tick(c)?;
            let arguments = pack(
                case.arguments
                    .iter()
                    .map(|v| v.at(None, c))
                    .collect::<Result<_, _>>()?,
            );
            let output = if left { &case.left } else { &case.right };
            rows.push(Scalar::Tuple(vec![
                arguments,
                output.presentation(&coordinates, c)?,
            ]));
        }
        let element = rows.first().map(Scalar::ty).unwrap_or(Type::Unit);
        Ok(Scalar::List {
            element,
            items: rows,
        })
    }
}
impl Value {
    fn presentation(
        &self,
        axes: &[forms::TermArgument],
        c: &Control,
    ) -> Result<Scalar, ValidationFailure> {
        fn element(ty: &Type, c: &Control) -> Result<Type, ValidationFailure> {
            stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
                tick(c)?;
                Ok(match ty {
                    Type::Z | Type::Q => {
                        Type::Tuple(vec![ty.clone(), Type::List(Box::new(ty.clone()))])
                    }
                    Type::Tuple(ts) => {
                        Type::Tuple(ts.iter().map(|t| element(t, c)).collect::<Result<_, _>>()?)
                    }
                    Type::List(t) => Type::List(Box::new(element(t, c)?)),
                    _ => ty.clone(),
                })
            })
        }
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            Ok(match self {
                Self::Number(f) => f.term_coordinates(axes, c)?,
                Self::Known(v) => v.clone(),
                Self::Tuple(v) => Scalar::Tuple(
                    v.iter()
                        .map(|v| v.presentation(axes, c))
                        .collect::<Result<_, _>>()?,
                ),
                Self::List { element: t, items } => Scalar::List {
                    element: element(t, c)?,
                    items: items
                        .iter()
                        .map(|v| v.presentation(axes, c))
                        .collect::<Result<_, _>>()?,
                },
                Self::Unsupported(_) => return Err("算法外値を正規形表示にできない".into()),
            })
        })
    }
}
