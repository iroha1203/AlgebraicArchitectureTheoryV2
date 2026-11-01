//! 元の有理parameter上で作用とLawを正規化し、完全な線形fiberを求める。
use super::change_affine::{Pending, with_missing};
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
    pub axes: Vec<Parameter>,
    pub guard_fiber: Fiber,
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
#[derive(Clone, Copy)]
enum Axes<'a> {
    Parameters(&'a [Parameter]),
    State(&'a [Fact]),
}
impl Axes<'_> {
    fn len(self) -> usize {
        match self {
            Self::Parameters(v) => v.len(),
            Self::State(v) => v.len(),
        }
    }
}
fn coordinates(
    env: &Environment<'_>,
    id: usize,
    form: &Form,
    axes: Axes<'_>,
    missing: &mut Pending,
) -> Result<(Option<Scalar>, Vec<Scalar>), ValidationFailure> {
    (match axes {
        Axes::Parameters(axes) => form
            .rational_coordinates(axes, &env.control)?
            .map(|(v, row)| (Some(v), row)),
        Axes::State(slots) => {
            missing.facts.extend(form.missing_facts());
            form.rational_state_coordinates(slots, &env.control)?
        }
    })
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
    axes: Axes<'_>,
    matrix: &mut Matrix,
    rhs: &mut Vec<Option<Scalar>>,
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
                rhs.push(Some(numeric::literal("1", &Type::Q, &env.control)?));
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
                    .as_ref()
                    .filter(|p| p.op == BinOp::Eq && p.bound_axes.is_empty())
                else {
                    if change_affine::numeric_condition(env, id, &v)? {
                        missing.unsupported=Some("numeric_change_condition");
                    }
                    return Err(unsupported(
                        env,
                        id,
                        "有理changeの全解は既知係数のアフィン等式の連言を要する",
                    ));
                };
                let form = affine::binary(BinOp::Sub, Some(&p.left), Some(&p.right), &env.control)?
                    .ok_or("有理等式の差がない")?;
                if form.varies_over(&missing.universal, &env.control)? {
                    matrix.push(vec![numeric::zero(&Type::Q, &env.control)?; axes.len()]);
                    rhs.push(Some(numeric::literal("1", &Type::Q, &env.control)?));
                    return Ok(());
                }
                let (constant, coefficients) = coordinates(env, id, &form, axes, missing)?;
                matrix.push(coefficients);
                rhs.push(
                    constant
                        .as_ref()
                        .map(|constant| {
                            numeric::binary(
                                BinOp::Sub,
                                &numeric::zero(&Type::Q, &env.control)?,
                                constant,
                                &env.control,
                            )
                        })
                        .transpose()?,
                );
                Ok(())
            }
        }
    })
}

/// Local declarations use the same rational equation extraction and full fiber.
pub(super) fn parameter_guard_domain(
    env: &Environment<'_>,
    guard: Option<usize>,
    vars: &BTreeMap<String, SourceValue>,
    axes: &[Parameter],
    reading: &str,
    missing: &mut Pending,
) -> Result<(Matrix, Vec<Scalar>, Fiber), ValidationFailure> {
    if axes.iter().any(|axis| axis.kind != NumberType::Q) {
        return Err("rational guard requires Q parameters".into());
    }
    let mut matrix = vec![];
    let mut rhs = vec![];
    if let Some(id) = guard {
        missing.expression = Some(id);
        let value = env.scoped_ast(id, vars, &Scope::default(), reading)?;
        missing.support.extend(value.support);
        missing.scope.merge(&value.scope);
        equations(
            env,
            id,
            vars,
            reading,
            Axes::Parameters(axes),
            &mut matrix,
            &mut rhs,
            missing,
        )?;
    }
    let rhs = rhs
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or("rational guard constant is undetermined")?;
    let fiber = field_fiber::solve(&Type::Q, &matrix, axes.len(), &rhs, &env.control)?;
    Ok((matrix, rhs, fiber))
}

pub(in crate::observed) fn compute(
    env: &Environment<'_>,
    change: &Declaration,
    subjects: &[Scalar],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<Linear, ValidationFailure> {
    with_missing(env, missing, |missing| {
        compute_inner(env, change, subjects, requirements, missing)
    })
}
fn compute_inner(
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
                Axes::Parameters(&axes),
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
                            if change_affine::numeric_condition(env, *cond, &v)? {
                                missing.unsupported=Some("numeric_change_condition");
                            }
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
                            if matches!(env.inputs.law().expr_type(*id), Some(Type::Q)) {
                                missing.unsupported=Some("nonlinear_numeric_change");
                            }
                            unsupported(env, *id, "有理changeの更新式がQアフィンでない")
                        })?;
                        coordinates(env, *id, &form, Axes::Parameters(&axes), missing)?;
                        let position = Fact {
                            snapshot: snapshot.clone(),
                            subject: subject.clone(),
                            field: Some(env.input_name(&format!("{entity}.{}", field.name))?),
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
        let (constant, row) = coordinates(env, *body, form, Axes::Parameters(&axes), missing)?;
        slots.push(slot.clone());
        action.push(row);
        offset.push(constant.ok_or("有理作用の固定項が未確定")?);
    }

    let mut guard_rhs = guard_rhs
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or("有理guardの固定項が未確定")?;
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
        with_missing(&updated, missing, |missing| {
            requirement_equations(&updated, Axes::Parameters(&axes), requirements, missing)
        })?
    };
    guard_matrix.extend(matrix);
    guard_rhs.extend(
        rhs.into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or("有理要求の固定項が未確定")?,
    );
    let fiber = field_fiber::solve(
        &Type::Q,
        &guard_matrix,
        axes.len(),
        &guard_rhs,
        &env.control,
    )?;
    Ok(Linear {
        parameter_count: axes.len(),
        axes,
        guard_fiber,
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
pub(in crate::observed) fn state_equations(
    env: &Environment<'_>,
    slots: &[Fact],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<(Matrix, Vec<Option<Scalar>>), ValidationFailure> {
    let mut state = Environment::with_primitive_valuation(
        env.inputs,
        &env.fixed_values(),
        &mut env.control.clone(),
    )?;
    state.object = env.object_domain();
    for slot in slots {
        env.tick()?;
        if env
            .field(
                &slot.snapshot,
                &slot.subject,
                slot.field.as_ref().ok_or("自由位置にfieldがない")?,
            )?
            .ty
            .erase()
            != Type::Q
        {
            return Err("有理局所状態の自由位置がQでない".into());
        }
        state.affine_valuation.insert(
            slot.clone(),
            Form::typed_state(&Type::Q, slot, &env.control)?,
        );
    }
    with_missing(&state, missing, |missing| {
        requirement_equations(&state, Axes::State(slots), requirements, missing)
    })
}
fn requirement_equations(
    env: &Environment<'_>,
    axes: Axes<'_>,
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<(Matrix, Vec<Option<Scalar>>), ValidationFailure> {
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
        for (name, v) in bindings {
            let p = law_params.iter().find(|p| p.name == *name).ok_or("有理Lawの束縛名が異なる")?;
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
        let (vars, universal) = change_affine::law_variables(env, law_params, bindings)?;
        missing.universal = universal;
        if let Some(guard) = guard {
            let v = env.scoped_ast(*guard, &vars, &Scope::default(), &law.reading)?;
            usable(env, *guard, &v)?;
            match v.known_value {
                Some(Scalar::Bool(false)) => continue,
                Some(Scalar::Bool(true)) => {}
                _ => {
                    missing.expression = Some(*guard);
                    missing.bindings = bindings.clone();
                    missing.parameters = law_params.iter()
                        .filter(|p| !bindings.iter().any(|(name, _)| *name == p.name))
                        .map(|p| (p.name.clone(), p.ty.clone()))
                        .collect();
                    if change_affine::numeric_condition(env, *guard, &v)? {
                        missing.unsupported=Some("numeric_change_condition");
                    }
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
        missing.parameters = law_params.iter().filter(|p| !bindings.iter().any(|(n,_)| *n == p.name))
            .map(|p| (p.name.clone(), p.ty.clone())).collect();
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
