//! 元の有理parameter上で作用とLawを正規化し、完全な線形fiberを求める。
use super::change_affine::Pending;
use super::*;
use crate::law::model::{Declaration, Signature};
use crate::observed::{
    affine::{self, Form, NumberType, Parameter},
    field_fiber::{self, Fiber, Matrix},
    numeric,
};
#[derive(Clone, Debug)]
pub(in crate::observed) struct Linear {
    pub parameter_count: usize,
    pub particular: Option<Vec<Scalar>>,
    pub kernel: Matrix,
    pub slots: Vec<Fact>,
    pub action: Matrix,
    pub offset: Vec<Scalar>,
    pub equations: Matrix,
    pub rhs: Vec<Scalar>,
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
        return Err(unsupported(env, id, "有理changeの式の構成条件が未成立"));
    }
    Ok(())
}
fn coordinates(
    env: &Environment<'_>,
    id: usize,
    form: &Form,
    axes: &[Parameter],
    missing: &mut Pending,
) -> Result<(Scalar, Vec<Scalar>), ValidationFailure> {
    form.rational_coordinates(axes, &env.control)?
        .ok_or_else(|| {
            missing.facts.extend(form.missing_facts());
            unsupported(
                env,
                id,
                "有理changeの係数に欠測または元parameter以外の記号がある",
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
    rhs: &mut Vec<Scalar>,
    missing: &mut Pending,
) -> Result<(), ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        let base = Scope::default();
        let v = env.scoped_ast(id, vars, &base, reading)?;
        usable(env, id, &v)?;
        if let Some(Scalar::Bool(holds)) = v.known_value {
            if !holds {
                matrix.push(vec![numeric::zero(&Type::Q, &env.control)?; axes.len()]);
                rhs.push(numeric::literal("1", &Type::Q, &env.control)?);
            }
            return Ok(());
        }
        match &env.inputs.law().exprs[id].kind {
            ExprKind::Group(body) => {
                equations(env, *body, vars, reading, axes, matrix, rhs, missing)
            }
            ExprKind::Let { name, value, body } => {
                let mut vars = vars.clone();
                let v = env.scoped_ast(*value, &vars, &base, reading)?;
                usable(env, *value, &v)?;
                vars.insert(name.name.clone(), v);
                equations(env, *body, &vars, reading, axes, matrix, rhs, missing)
            }
            ExprKind::Binary {
                op: BinOp::And,
                lhs,
                rhs: right,
            } => {
                equations(env, *lhs, vars, reading, axes, matrix, rhs, missing)?;
                equations(env, *right, vars, reading, axes, matrix, rhs, missing)
            }
            _ => {
                let Some(p) = v
                    .comparison
                    .filter(|p| p.op == BinOp::Eq && p.bound_axes.is_empty())
                else {
                    guard_missing(env, id, vars, reading, missing)?;
                    return Err(unsupported(
                        env,
                        id,
                        "有理changeの全解は既知係数のアフィン等式の連言を要する",
                    ));
                };
                let form = affine::binary(BinOp::Sub, Some(&p.left), Some(&p.right), &env.control)?
                    .ok_or("有理等式の差がない")?;
                let (constant, coefficients) = coordinates(env, id, &form, axes, missing)?;
                matrix.push(coefficients);
                rhs.push(numeric::binary(
                    BinOp::Sub,
                    &numeric::zero(&Type::Q, &env.control)?,
                    &constant,
                    &env.control,
                )?);
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
    missing: &mut Pending,
) -> Result<Linear, ValidationFailure> {
    missing.coefficient_type = Some(Type::Q);
    let Signature::Change {
        params,
        guard,
        body,
    } = &change.signature
    else {
        return Err("有理候補がchangeでない".into());
    };
    if params.is_empty() || params[1..].iter().any(|p| p.ty != Type::Q) {
        return Err(unsupported(
            env,
            *body,
            "有理changeの混合parameter型は未実装",
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
                kind: NumberType::Q,
            });
        }
    }
    let mut updates = BTreeMap::<Fact, Form>::new();
    let mut guard_matrix = vec![];
    let mut guard_rhs = vec![];
    for (i, subject) in subjects.iter().enumerate() {
        let mut vars = BTreeMap::from([(params[0].name.clone(), value(env, subject.clone())?)]);
        for (p, axis) in params[1..]
            .iter()
            .zip(&axes[i * (params.len() - 1)..(i + 1) * (params.len() - 1)])
        {
            env.tick()?;
            let mut v = value(env, numeric::zero(&Type::Q, &env.control)?)?;
            v.known_value = None;
            v.scalar_scope = None;
            v.affine = affine::parameter(&Type::Q, axis, &env.control)?.map(Box::new);
            vars.insert(p.name.clone(), v);
        }
        missing.bindings = vec![(params[0].name.clone(), subject.clone())];
        missing.parameters = params[1..]
            .iter()
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect();
        if let Some(guard) = guard {
            missing.expression = Some(*guard);
            equations(
                env,
                *guard,
                &vars,
                &change.reading,
                &axes,
                &mut guard_matrix,
                &mut guard_rhs,
                missing,
            )?;
        }
        missing.expression = Some(*body);
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
                            missing.expression = Some(*cond);
                            guard_missing(env, *cond, &vars, &change.reading, missing)?;
                            return Err(unsupported(env, *cond, "有理changeの未確定分岐は未実装"));
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
                        return Err(unsupported(env, *base, "有理changeの更新先が未確定"));
                    };
                    for (field, id) in fields {
                        let v = env.scoped_ast(*id, &vars, &Scope::default(), &change.reading)?;
                        usable(env, *id, &v)?;
                        let form = v.affine.ok_or_else(|| {
                            unsupported(env, *id, "有理changeの更新式がQアフィンでない")
                        })?;
                        coordinates(env, *id, &form, &axes, missing)?;
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
                                    "有理changeの同時更新衝突のfiberは未実装",
                                ));
                            }
                        } else {
                            updates.insert(position, *form);
                        }
                    }
                    break;
                }
                _ => return Err("有理changeのwithがない".into()),
            }
        }
    }
    let mut slots = vec![];
    let mut action = vec![];
    let mut offset = vec![];
    for (slot, form) in &updates {
        let (constant, row) = coordinates(env, *body, form, &axes, missing)?;
        slots.push(slot.clone());
        action.push(row);
        offset.push(constant);
    }

    let guard_fiber = field_fiber::solve(
        &Type::Q,
        &guard_matrix,
        axes.len(),
        &guard_rhs,
        &env.control,
    )?;
    let candidates_empty = guard_fiber.particular.is_none();
    let mut updated = Environment::with_primitive_valuation(
        env.inputs,
        &env.fixed_values(),
        &mut env.control.clone(),
    )?;
    updated.object = env.object_domain();
    updated.affine_valuation = updates;
    let (matrix, rhs) = if candidates_empty {
        (vec![], vec![])
    } else {
        requirement_equations(&updated, &axes, requirements, missing)?
    };
    guard_matrix.extend(matrix);
    guard_rhs.extend(rhs);
    let fiber = field_fiber::solve(
        &Type::Q,
        &guard_matrix,
        axes.len(),
        &guard_rhs,
        &env.control,
    )?;
    Ok(Linear {
        parameter_count: axes.len(),
        particular: fiber.particular.clone(),
        kernel: fiber.kernel.clone(),
        slots,
        action,
        offset,
        equations: guard_matrix,
        rhs: guard_rhs,
        fiber,
    })
}
// 未確定guardの実評価で残った原始位置を、元のguard Sourceへ結び付ける。
fn guard_missing(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    reading: &str,
    missing: &mut Pending,
) -> Result<(), ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        let v = env.scoped_ast(id, vars, &Scope::default(), reading)?;
        if v.known_value.is_some() {
            return Ok(());
        }
        if let Some(form) = &v.affine {
            missing.facts.extend(form.missing_facts());
        }
        if let Some(comparison) = &v.comparison {
            missing.facts.extend(comparison.left.missing_facts());
            missing.facts.extend(comparison.right.missing_facts());
        }
        match &env.inputs.law().exprs[id].kind {
            ExprKind::Group(body) => guard_missing(env, *body, vars, reading, missing)?,
            ExprKind::Let { name, value, body } => {
                let mut vars = vars.clone();
                vars.insert(
                    name.name.clone(),
                    env.scoped_ast(*value, &vars, &Scope::default(), reading)?,
                );
                guard_missing(env, *body, &vars, reading, missing)?;
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                guard_missing(env, *lhs, vars, reading, missing)?;
                guard_missing(env, *rhs, vars, reading, missing)?;
            }
            ExprKind::Unary { operand, .. } => {
                guard_missing(env, *operand, vars, reading, missing)?
            }
            _ => {}
        }
        Ok(())
    })
}
fn requirement_equations(
    env: &Environment<'_>,
    axes: &[Parameter],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<(Matrix, Vec<Scalar>), ValidationFailure> {
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
            return Err("有理候補の要求がLawでない".into());
        };
        let mut checked = BTreeMap::new();
        let mut checks = owned_call::Checks::default();
        for (p, (name, v)) in law_params.iter().zip(bindings) {
            if p.name != *name {
                return Err("有理Lawの束縛順が異なる".into());
            }
            env.owned_call_value_check(
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
            return Err(unsupported(env, *body, "有理Lawの適用条件が未確定"));
        }
        let vars = bindings
            .iter()
            .map(|(n, v)| Ok((n.clone(), value(env, v.clone())?)))
            .collect::<Result<BTreeMap<_, _>, ValidationFailure>>()?;
        if let Some(guard) = guard {
            let v = env.scoped_ast(*guard, &vars, &Scope::default(), &law.reading)?;
            usable(env, *guard, &v)?;
            match v.known_value {
                Some(Scalar::Bool(false)) => continue,
                Some(Scalar::Bool(true)) => {}
                _ => {
                    missing.expression = Some(*guard);
                    missing.bindings = bindings.clone();
                    missing.parameters.clear();
                    guard_missing(env, *guard, &vars, &law.reading, missing)?;
                    return Err(unsupported(
                        env,
                        *guard,
                        "有理候補で未確定のLaw guardの全解は未実装",
                    ));
                }
            }
        }
        missing.expression = Some(*body);
        missing.bindings = bindings.clone();
        missing.parameters.clear();
        equations(
            env,
            *body,
            &vars,
            &law.reading,
            axes,
            &mut matrix,
            &mut rhs,
            missing,
        )?;
    }
    Ok((matrix, rhs))
}
