//! Termの共通制御構造。値の演算と未知条件の解釈は各評価系が所有する。
use super::*;
use crate::law::ast::UnOp;

pub(super) trait Interpretation {
    type Value: Clone;
    fn item_tick(c: &Control) -> Result<(), ValidationFailure>;
    fn select_match(
        term: &Term,
        arms: &[crate::law::ast::Arm],
        input: Self::Value,
        vars: &BTreeMap<String, Self::Value>,
        law: &CheckedLaw,
        c: &Control,
    ) -> Result<Option<(usize, BTreeMap<String, Self::Value>)>, ValidationFailure>;
    fn unmatched(ty: &Type) -> Result<Self::Value, ValidationFailure>;
    fn tuple(values: Vec<Self::Value>) -> Self::Value;
    fn list_type(ty: &Type) -> Result<Type, ValidationFailure>;
    fn list(element: Type, values: Vec<Self::Value>) -> Self::Value;
    fn project(
        value: Self::Value,
        index: usize,
        ty: &Type,
    ) -> Result<Self::Value, ValidationFailure>;
    fn eval(
        term: &Term,
        id: usize,
        vars: &BTreeMap<String, Self::Value>,
        law: &CheckedLaw,
        c: &Control,
    ) -> Result<Self::Value, ValidationFailure>;
    fn bind(
        vars: &BTreeMap<String, Self::Value>,
        name: &str,
        value: Self::Value,
        c: &Control,
    ) -> Result<BTreeMap<String, Self::Value>, ValidationFailure>;
    fn unary(
        op: UnOp,
        value: Self::Value,
        ty: &Type,
        law: &CheckedLaw,
        span: Span,
        c: &Control,
    ) -> Result<Self::Value, ValidationFailure>;
    fn short(
        op: BinOp,
        value: &Self::Value,
        c: &Control,
    ) -> Result<Option<Self::Value>, ValidationFailure>;
    fn binary(
        op: BinOp,
        left: Self::Value,
        right: Self::Value,
        ty: &Type,
        law: &CheckedLaw,
        span: Span,
        c: &Control,
    ) -> Result<Self::Value, ValidationFailure>;
    fn condition(value: Self::Value, c: &Control) -> Result<Option<bool>, ValidationFailure>;
    fn join(
        left: Self::Value,
        right: Self::Value,
        ty: &Type,
        law: &CheckedLaw,
        c: &Control,
    ) -> Result<Self::Value, ValidationFailure>;
}

pub(super) fn expression<I: Interpretation>(
    term: &Term,
    e: &Expr,
    ty: &Type,
    vars: &BTreeMap<String, I::Value>,
    law: &CheckedLaw,
    c: &Control,
) -> Result<Option<I::Value>, ValidationFailure> {
    Ok(Some(match &e.kind {
        ExprKind::Match { scrutinee, arms } => {
            let input = I::eval(term, *scrutinee, vars, law, c)?;
            match I::select_match(term, arms, input, vars, law, c)? {
                Some((body, local)) => I::eval(term, body, &local, law, c)?,
                None => I::unmatched(ty)?,
            }
        }
        ExprKind::Tuple(children) => I::tuple(items::<I>(term, children, vars, law, c)?),
        ExprKind::ListLit {
            items: children, ..
        } => {
            let element = I::list_type(ty)?;
            I::list(element, items::<I>(term, children, vars, law, c)?)
        }
        ExprKind::Index { base, index, .. } => {
            I::project(I::eval(term, *base, vars, law, c)?, *index, ty)?
        }
        ExprKind::Group(body) => I::eval(term, *body, vars, law, c)?,
        ExprKind::Let { name, value, body } => {
            let value = I::eval(term, *value, vars, law, c)?;
            let local = I::bind(vars, &name.name, value, c)?;
            I::eval(term, *body, &local, law, c)?
        }
        ExprKind::Unary { op, operand } => {
            let value = I::eval(term, *operand, vars, law, c)?;
            I::unary(*op, value, ty, law, e.span, c)?
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let left = I::eval(term, *lhs, vars, law, c)?;
            if let Some(value) = I::short(*op, &left, c)? {
                value
            } else {
                let right = I::eval(term, *rhs, vars, law, c)?;
                I::binary(*op, left, right, ty, law, e.span, c)?
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let condition = I::eval(term, *cond, vars, law, c)?;
            match I::condition(condition, c)? {
                Some(take) => I::eval(
                    term,
                    if take { *then_branch } else { *else_branch },
                    vars,
                    law,
                    c,
                )?,
                None => {
                    let left = I::eval(term, *then_branch, vars, law, c)?;
                    let right = I::eval(term, *else_branch, vars, law, c)?;
                    I::join(left, right, ty, law, c)?
                }
            }
        }
        _ => return Ok(None),
    }))
}

pub(super) fn items<I: Interpretation>(
    term: &Term,
    children: &[usize],
    vars: &BTreeMap<String, I::Value>,
    law: &CheckedLaw,
    c: &Control,
) -> Result<Vec<I::Value>, ValidationFailure> {
    let mut values = Vec::new();
    for child in children {
        I::item_tick(c)?;
        values.push(I::eval(term, *child, vars, law, c)?);
        I::item_tick(c)?;
    }
    Ok(values)
}

/// 既知のscrutineeは宣言順に枝を調べ、最初に合う枝だけを評価する。
pub(super) fn select_arm<V>(
    arms: &[crate::law::ast::Arm],
    c: &Control,
    mut bind: impl FnMut(&Pattern) -> Result<Option<V>, ValidationFailure>,
) -> Result<Option<(usize, V)>, ValidationFailure> {
    for arm in arms {
        tick(c)?;
        if let Some(local) = bind(&arm.pattern)? {
            return Ok(Some((arm.body, local)));
        }
    }
    Ok(None)
}

/// 有限域のbodyを順に読み、反例/証人で短絡する。未知のbodyは解釈側がNoneを返す。
pub(super) fn quantifier(
    kind: QuantKind,
    values: Vec<Scalar>,
    c: &Control,
    mut body: impl FnMut(Scalar) -> Result<Option<bool>, ValidationFailure>,
) -> Result<Option<bool>, ValidationFailure> {
    let mut result = Some(kind == QuantKind::Forall);
    for value in values {
        tick(c)?;
        match body(value)? {
            Some(b) if (kind == QuantKind::Forall && !b) || (kind == QuantKind::Exists && b) => {
                return Ok(Some(b));
            }
            None => result = None,
            _ => {}
        }
    }
    Ok(result)
}
