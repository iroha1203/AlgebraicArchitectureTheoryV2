//! 通常の式評価器から整数changeの作用と選択Lawの線形系を得る。
use super::*;
use crate::law::model::{Declaration, Signature};
use crate::observed::{
    affine::{self, Form, NumberType, Parameter},
    integer_fiber::{self, Fiber, Matrix},
};
use num_bigint::BigInt as Z;
use num_traits::{One, Zero};

#[derive(Clone, Debug)]
pub(in crate::observed) struct Linear {
    pub slots: Vec<Fact>,
    pub action: Matrix,
    pub offset: Vec<Z>,
    pub equations: Matrix,
    pub rhs: Vec<Z>,
    pub fiber: Fiber,
}
fn unsupported(env: &Environment<'_>, id: usize, feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law {
            span: env.inputs.law().exprs[id].span,
        },
        feature: feature.into(),
    }
}
fn value(env: &Environment<'_>, scalar: Scalar) -> Result<SourceValue, ValidationFailure> {
    Ok(SourceValue {
        condition_failed: false,
        condition_pending: false,
        symbolic: None,
        comparison: None,
        affine: affine::constant(&scalar, &env.control)?.map(Box::new),
        scope: Scope::default(),
        known_value: Some(scalar),
        support: vec![],
        scalar_scope: Some(Scope::default()),
    })
}
fn usable(env: &Environment<'_>, id: usize, v: &SourceValue) -> Result<(), ValidationFailure> {
    if v.condition_failed || v.condition_pending {
        return Err(unsupported(env, id, "整数changeの式の構成条件が未成立"));
    }
    Ok(())
}
fn coordinates(
    env: &Environment<'_>,
    id: usize,
    form: &Form,
    axes: &[Parameter],
) -> Result<(Z, Vec<Z>), ValidationFailure> {
    form.integer_coordinates(axes, &env.control)?
        .ok_or_else(|| {
            unsupported(
                env,
                id,
                "整数changeの係数に欠測または元parameter以外の記号がある",
            )
        })
}
fn equations(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    reading: &str,
    axes: &[Parameter],
    matrix: &mut Matrix,
    rhs: &mut Vec<Z>,
) -> Result<(), ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        let base = Scope::default();
        let v = env.scoped_ast(id, vars, &base, reading)?;
        usable(env, id, &v)?;
        if let Some(Scalar::Bool(holds)) = v.known_value {
            if !holds {
                matrix.push(vec![Z::zero(); axes.len()]);
                rhs.push(Z::one());
            }
            return Ok(());
        }
        match &env.inputs.law().exprs[id].kind {
            ExprKind::Group(body) => equations(env, *body, vars, reading, axes, matrix, rhs),
            ExprKind::Let { name, value, body } => {
                let mut vars = vars.clone();
                let v = env.scoped_ast(*value, &vars, &base, reading)?;
                usable(env, *value, &v)?;
                vars.insert(name.name.clone(), v);
                equations(env, *body, &vars, reading, axes, matrix, rhs)
            }
            ExprKind::Binary {
                op: BinOp::And,
                lhs,
                rhs: right,
            } => {
                equations(env, *lhs, vars, reading, axes, matrix, rhs)?;
                equations(env, *right, vars, reading, axes, matrix, rhs)
            }
            _ => {
                let Some(p) = v
                    .comparison
                    .filter(|p| p.op == BinOp::Eq && p.bound_axes.is_empty())
                else {
                    return Err(unsupported(
                        env,
                        id,
                        "整数changeの全解は既知係数のアフィン等式の連言を要する",
                    ));
                };
                let form = affine::binary(BinOp::Sub, Some(&p.left), Some(&p.right), &env.control)?
                    .ok_or("整数等式の差がない")?;
                let (constant, coefficients) = coordinates(env, id, &form, axes)?;
                matrix.push(coefficients);
                rhs.push(-constant);
                Ok(())
            }
        }
    })
}

pub(in crate::observed) fn compute(
    env: &Environment<'_>,
    change: &Declaration,
    subjects: &[Scalar],
    requirements: &[(String, Vec<(String, Scalar)>)],
) -> Result<Linear, ValidationFailure> {
    let Signature::Change {
        params,
        guard,
        body,
    } = &change.signature
    else {
        return Err("整数候補がchangeでない".into());
    };
    if params.is_empty() || params[1..].iter().any(|p| p.ty != Type::Z) {
        return Err(unsupported(
            env,
            *body,
            "整数changeの混合parameter型は未実装",
        ));
    }
    let mut axes = vec![];
    for (i, _) in subjects.iter().enumerate() {
        for p in &params[1..] {
            env.tick()?;
            axes.push(Parameter {
                binder: p.span,
                name: p.name.clone(),
                context: crate::observed::call::Context {
                    instance: Some(i),
                    ..Default::default()
                },
                kind: NumberType::Z,
            });
        }
    }
    let mut updates = BTreeMap::<Fact, Form>::new();
    for (i, subject) in subjects.iter().enumerate() {
        let mut vars = BTreeMap::from([(params[0].name.clone(), value(env, subject.clone())?)]);
        for (p, axis) in params[1..]
            .iter()
            .zip(&axes[i * (params.len() - 1)..(i + 1) * (params.len() - 1)])
        {
            env.tick()?;
            let mut v = value(env, Scalar::Z(Z::zero()))?;
            v.known_value = None;
            v.scalar_scope = None;
            v.affine = affine::parameter(&Type::Z, axis, &env.control)?.map(Box::new);
            vars.insert(p.name.clone(), v);
        }
        if let Some(guard) = guard {
            let v = env.scoped_ast(*guard, &vars, &Scope::default(), &change.reading)?;
            usable(env, *guard, &v)?;
            if v.known_value != Some(Scalar::Bool(true)) {
                return Err(unsupported(
                    env,
                    *guard,
                    "整数changeのguard fiberへの再parameter化は未実装",
                ));
            }
        }
        let mut current = *body;
        loop {
            env.tick()?;
            match &env.inputs.law().exprs[current].kind {
                ExprKind::Group(inner) => current = *inner,
                ExprKind::Let { name, value, body } => {
                    let v = env.scoped_ast(*value, &vars, &Scope::default(), &change.reading)?;
                    usable(env, *value, &v)?;
                    vars.insert(name.name.clone(), v);
                    current = *body;
                }
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    let v = env.scoped_ast(*cond, &vars, &Scope::default(), &change.reading)?;
                    usable(env, *cond, &v)?;
                    current = match v.known_value {
                        Some(Scalar::Bool(true)) => *then_branch,
                        Some(Scalar::Bool(false)) => *else_branch,
                        _ => {
                            return Err(unsupported(
                                env,
                                *cond,
                                "整数changeのparameter依存分岐は未実装",
                            ));
                        }
                    };
                }
                ExprKind::With {
                    base,
                    updates: fields,
                } => {
                    let target =
                        env.scoped_ast(*base, &vars, &Scope::default(), &change.reading)?;
                    usable(env, *base, &target)?;
                    let Some(Scalar::Subject {
                        snapshot,
                        subject,
                        entity,
                    }) = &target.known_value
                    else {
                        return Err(unsupported(env, *base, "整数changeの更新先が未確定"));
                    };
                    for (field, id) in fields {
                        let v = env.scoped_ast(*id, &vars, &Scope::default(), &change.reading)?;
                        usable(env, *id, &v)?;
                        let form = v.affine.ok_or_else(|| {
                            unsupported(env, *id, "整数changeの更新式がZアフィンでない")
                        })?;
                        coordinates(env, *id, &form, &axes)?;
                        let position = Fact {
                            snapshot: snapshot.clone(),
                            subject: subject.clone(),
                            field: Some(format!("{entity}.{}", field.name)),
                            atom: None,
                        };
                        if let Some(prior) = updates.get(&position) {
                            if prior != form.as_ref() {
                                return Err(unsupported(
                                    env,
                                    *id,
                                    "整数changeの同時更新衝突のfiberは未実装",
                                ));
                            }
                        } else {
                            updates.insert(position, *form);
                        }
                    }
                    break;
                }
                _ => return Err("整数changeのwithがない".into()),
            }
        }
    }
    let mut slots = vec![];
    let mut action = vec![];
    let mut offset = vec![];
    for (slot, form) in &updates {
        let (constant, row) = coordinates(env, *body, form, &axes)?;
        slots.push(slot.clone());
        action.push(row);
        offset.push(constant);
    }
    let assignments = env
        .primitive_valuation
        .as_ref()
        .map(|v| {
            v.iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let mut updated =
        Environment::with_primitive_valuation(env.inputs, &assignments, &mut env.control.clone())?;
    updated.object = env.object_domain();
    updated.affine_valuation = updates;
    let mut matrix = vec![];
    let mut rhs = vec![];
    for (name, bindings) in requirements {
        let law = &env.inputs.law().declarations[name];
        let Signature::Law {
            body,
            guard,
            params: law_params,
            ..
        } = &law.signature
        else {
            return Err("整数候補の要求がLawでない".into());
        };
        let mut checked = BTreeMap::new();
        let mut checks = owned_call::Checks::default();
        for (p, (name, v)) in law_params.iter().zip(bindings) {
            if p.name != *name {
                return Err("整数Lawの束縛順が異なる".into());
            }
            updated.owned_call_value_check(
                &p.ty,
                &crate::observed::term::affine::Value::Known(v.clone()),
                &checked,
                &law.reading,
                law.span,
                &mut checks,
            )?;
            checked.insert(name.as_str(), Some(v));
        }
        if checks.failure.is_some() {
            continue;
        }
        if checks.blocked {
            return Err(unsupported(&updated, *body, "整数Lawの適用条件が未確定"));
        }
        let vars = bindings
            .iter()
            .map(|(n, v)| Ok((n.clone(), value(&updated, v.clone())?)))
            .collect::<Result<BTreeMap<_, _>, ValidationFailure>>()?;
        if let Some(guard) = guard {
            let v = updated.scoped_ast(*guard, &vars, &Scope::default(), &law.reading)?;
            usable(&updated, *guard, &v)?;
            match v.known_value {
                Some(Scalar::Bool(false)) => continue,
                Some(Scalar::Bool(true)) => {}
                _ => {
                    return Err(unsupported(
                        &updated,
                        *guard,
                        "整数候補で変化するLaw guardの全解は未実装",
                    ));
                }
            }
        }
        equations(
            &updated,
            *body,
            &vars,
            &law.reading,
            &axes,
            &mut matrix,
            &mut rhs,
        )?;
    }
    let fiber = integer_fiber::solve(&matrix, axes.len(), &rhs, &env.control)?;
    Ok(Linear {
        slots,
        action,
        offset,
        equations: matrix,
        rhs,
        fiber,
    })
}
