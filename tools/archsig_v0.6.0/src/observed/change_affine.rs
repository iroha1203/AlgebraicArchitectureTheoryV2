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
pub(in crate::observed) struct Guard {
    pub equations: Matrix,
    pub rhs: Vec<Z>,
    pub fiber: Fiber,
}
#[derive(Clone, Debug)]
pub(in crate::observed) struct Linear {
    pub parameter_count: usize,
    pub axes: Vec<Parameter>,
    pub candidates_empty: bool,
    pub guard: Option<Guard>,
    pub particular: Option<Vec<Z>>,
    pub kernel: Matrix,
    pub slots: Vec<Fact>,
    pub action: Matrix,
    pub offset: Vec<Z>,
    pub equations: Matrix,
    pub rhs: Vec<Z>,
    pub fiber: Fiber,
}
#[derive(Default)]
pub(in crate::observed) struct Pending {
    pub universal: Vec<Parameter>,
    pub coefficient_type: Option<Type>,
    pub facts: Vec<Fact>,
    pub expression: Option<usize>,
    pub bindings: Vec<(String, Scalar)>,
    pub parameters: Vec<(String, Type)>,
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
/// 未束縛の数値Law引数は標本値ではなく、元binderの全域記号として評価する。
pub(super) fn law_variables(
    env: &Environment<'_>, params: &[crate::law::model::Param], bindings: &[(String, Scalar)],
) -> Result<(BTreeMap<String, SourceValue>, Vec<Parameter>), ValidationFailure> {
    let mut names = std::collections::BTreeSet::new();
    for (name, scalar) in bindings {
        env.tick()?;
        if !names.insert(name) || !params.iter().any(|p| p.name == *name && p.ty.erase() == scalar.ty()) {
            return Err("Law束縛の名前・型または重複が不正".into());
        }
    }
    let mut vars = BTreeMap::new();
    let mut universal = vec![];
    for p in params {
        env.tick()?;
        if let Some((_, scalar)) = bindings.iter().find(|(name, _)| *name == p.name) {
            vars.insert(p.name.clone(), value(env, scalar.clone())?);
        } else {
            let kind = match p.ty.erase() {
                Type::Z => NumberType::Z, Type::Q => NumberType::Q,
                _ => return Err("未束縛の局所Law引数がZ/Qでない".into()),
            };
            let parameter = Parameter { binder: p.span, name: p.name.clone(), context: env.context.get().unwrap_or_default(), kind };
            let mut v = value(env, numeric::zero(&kind.ty(), &env.control)?)?;
            v.known_value = None;
            v.scalar_scope = None;
            v.affine = affine::parameter(&kind.ty(), &parameter, &env.control)?.map(Box::new);
            vars.insert(p.name.clone(), v);
            universal.push(parameter);
        }
    }
    Ok((vars, universal))
}
fn usable(env: &Environment<'_>, id: usize, v: &SourceValue) -> Result<(), ValidationFailure> {
    if v.condition_failed || v.condition_pending {
        return Err(unsupported(env, id, "整数changeの式の構成条件が未成立"));
    }
    Ok(())
}
#[derive(Clone, Copy)]
enum Axes<'a> { Parameters(&'a [Parameter]), State(&'a [Fact]) }
impl Axes<'_> {
    fn len(self) -> usize { match self { Self::Parameters(xs) => xs.len(), Self::State(xs) => xs.len() } }
}
fn coordinates(
    env: &Environment<'_>,
    id: usize,
    form: &Form,
    axes: Axes<'_>,
    missing: &mut Pending,
) -> Result<(Option<Z>, Vec<Z>), ValidationFailure> {
    (match axes {
        Axes::Parameters(xs) => form.integer_coordinates(xs, &env.control)?.map(|(v,row)|(Some(v),row)),
        Axes::State(xs) => { missing.facts.extend(form.missing_facts()); form.state_coordinates(xs, &env.control)? },
    }).ok_or_else(|| {
            missing.facts.extend(form.missing_facts());
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
    axes: Axes<'_>,
    matrix: &mut Matrix,
    rhs: &mut Vec<Option<Z>>,
    missing: &mut Pending,
) -> Result<(), ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        let base = Scope::default();
        let v = env.scoped_ast(id, vars, &base, reading)?;
        usable(env, id, &v)?;
        if let Some(Scalar::Bool(holds)) = v.known_value {
            if !holds {
                matrix.push(vec![Z::zero(); axes.len()]);
                rhs.push(Some(Z::one()));
            }
            return Ok(());
        }
        if v.comparison.is_none()
            && !missing.universal.is_empty()
            && let Some(forms) = parameter_coefficient_forms(env, id, vars, reading, &missing.universal)?
        {
            for form in forms {
                let (constant, coefficients) = coordinates(env, id, &form, axes, missing)?;
                matrix.push(coefficients);
                rhs.push(constant.map(|v| -v));
            }
            return Ok(());
        }
        match &env.inputs.law().exprs[id].kind {
            ExprKind::Group(body) => equations(env, *body, vars, reading, axes, matrix, rhs, missing),
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
                    return Err(unsupported(
                        env,
                        id,
                        "整数changeの全解は既知係数のアフィン等式の連言を要する",
                    ));
                };
                let form = affine::binary(BinOp::Sub, Some(&p.left), Some(&p.right), &env.control)?
                    .ok_or("整数等式の差がない")?;
                if form.varies_over(&missing.universal, &env.control)? {
                    matrix.push(vec![Z::zero(); axes.len()]);
                    rhs.push(Some(Z::one()));
                    return Ok(());
                }
                let (constant, coefficients) = coordinates(env, id, &form, axes, missing)?;
                matrix.push(coefficients);
                rhs.push(constant.map(|v|-v));
                Ok(())
            }
        }
    })
}

fn parameter_coefficient_forms(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    reading: &str,
    universal: &[Parameter],
) -> Result<Option<Vec<Form>>, ValidationFailure> {
    let mut values = vec![];
    let mut parameters = vec![];
    for (name, value) in vars {
        env.tick()?;
        if value.condition_failed || value.condition_pending {
            return Ok(None);
        }
        if let Some(value) = &value.known_value {
            values.push((name.clone(), value.clone()));
        } else if let Some(form) = &value.affine {
            parameters.push((name.clone(), form.as_ref().clone()));
        } else {
            return Ok(None);
        }
    }
    let Some((ring, family)) =
        crate::observed::object_equation_presentation::parameter_difference_with_bindings(
            env.inputs,
            id,
            &values,
            &parameters,
            &mut env.control.clone(),
        )
        .map_err(|cause| match cause {
            crate::construction::ConstructionFailure::Stopped(stop) => {
                ValidationFailure::Stop(stop)
            }
            crate::construction::ConstructionFailure::InvalidSelection(message)
            | crate::construction::ConstructionFailure::Inconsistent(message) => {
                format!("数値Law係数: {message}").into()
            }
        })?
    else {
        return Ok(None);
    };
    if ring.ty != Type::Z
        || family
            .parameters
            .iter()
            .any(|(p, _)| !universal.contains(p))
    {
        return Ok(None);
    }
    let mut fields = vec![];
    for symbol in &ring.symbols {
        env.tick()?;
        let slot = &symbol.slot;
        if !slot.component.is_empty() {
            return Ok(None);
        }
        let subject = env.subject(&slot.snapshot, &slot.subject)?;
        let prefix = format!("{}.", subject.ty);
        let field = slot
            .field
            .strip_prefix(&prefix)
            .ok_or("係数のfieldが元subject型と違う")?;
        let base = value(
            env,
            Scalar::Subject {
                snapshot: slot.snapshot.clone(),
                subject: slot.subject.clone(),
                entity: subject.ty.clone(),
            },
        )?;
        let source = env.scoped_field(
            base,
            field,
            &Scope::default(),
            reading,
            env.inputs.law().exprs[id].span,
        )?;
        usable(env, id, &source)?;
        let Some(form) = source.affine else {
            return Ok(None);
        };
        fields.push(*form);
    }
    let mut forms = vec![];
    for coefficient in
        std::iter::once(&family.constant).chain(family.parameters.iter().map(|(_, p)| p))
    {
        env.tick()?;
        if coefficient.terms.is_empty() {
            continue;
        }
        let mut sum =
            affine::constant(&Scalar::Z(Z::zero()), &env.control)?.ok_or("係数の零がZでない")?;
        for term in &coefficient.terms {
            env.tick()?;
            let Some(mut product) = affine::constant(term.coefficient.scalar(), &env.control)?
            else {
                return Ok(None);
            };
            for &variable in &term.variables {
                let field = fields.get(variable).ok_or("係数の記号が範囲外")?;
                let Some(next) =
                    affine::binary(BinOp::Mul, Some(&product), Some(field), &env.control)?
                else {
                    return Ok(None);
                };
                product = next;
            }
            sum = affine::binary(BinOp::Add, Some(&sum), Some(&product), &env.control)?
                .ok_or("係数の和がない")?;
        }
        forms.push(sum);
    }
    Ok(Some(forms))
}
pub(in crate::observed) fn compute(
    env: &Environment<'_>,
    change: &Declaration,
    subjects: &[Scalar],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
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
    let mut guard_matrix = vec![];
    let mut guard_rhs = vec![];
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
        missing.bindings = vec![(params[0].name.clone(), subject.clone())];
        missing.parameters = params[1..].iter().map(|p| (p.name.clone(), p.ty.clone())).collect();
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
                        coordinates(env, *id, &form, Axes::Parameters(&axes), missing)?;
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
        let (constant, row) = coordinates(env, *body, form, Axes::Parameters(&axes), missing)?;
        slots.push(slot.clone());
        action.push(row);
        offset.push(constant.ok_or("作用の固定項が未確定")?);
    }
    let guard_rhs = guard_rhs.into_iter().collect::<Option<Vec<_>>>().ok_or("guardの固定項が未確定")?;
    let guard = if !guard_matrix.is_empty() {
        let fiber = integer_fiber::solve(&guard_matrix, axes.len(), &guard_rhs, &env.control)?;
        if fiber.particular.is_none() {
            return Ok(Linear {
                parameter_count: axes.len(),
                axes,
                candidates_empty: true,
                guard: None,
                particular: None,
                kernel: fiber.kernel.clone(),
                slots,
                action,
                offset,
                equations: guard_matrix,
                rhs: guard_rhs,
                fiber,
            });
        }
        Some(Guard {
            equations: guard_matrix,
            rhs: guard_rhs,
            fiber,
        })
    } else {
        None
    };
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
    let (mut matrix, rhs) = requirement_equations(&updated, Axes::Parameters(&axes), requirements, missing)?;
    let mut rhs = rhs.into_iter().collect::<Option<Vec<_>>>().ok_or("parameter方程式の固定項が未確定")?;
    let free_count = guard
        .as_ref()
        .map_or(axes.len(), |g| axes.len() - g.fiber.rank);
    if let Some(g) = &guard {
        let origin = g.fiber.particular.as_ref().ok_or("guardの特解がない")?;
        let shift = apply(&matrix, origin, &env.control)?;
        for (value, shift) in rhs.iter_mut().zip(shift) {
            *value -= shift;
        }
        matrix = compose(&matrix, &g.fiber.kernel, free_count, &env.control)?;
    }
    let fiber = integer_fiber::solve(&matrix, free_count, &rhs, &env.control)?;
    let (particular, kernel) = if let Some(g) = &guard {
        let particular = fiber
            .particular
            .as_ref()
            .map(|point| {
                let mut restored = apply(&g.fiber.kernel, point, &env.control)?;
                for (value, offset) in restored
                    .iter_mut()
                    .zip(g.fiber.particular.as_ref().ok_or("guardの特解がない")?)
                {
                    *value += offset;
                }
                Ok::<_, ValidationFailure>(restored)
            })
            .transpose()?;
        (
            particular,
            compose(
                &g.fiber.kernel,
                &fiber.kernel,
                free_count - fiber.rank,
                &env.control,
            )?,
        )
    } else {
        (fiber.particular.clone(), fiber.kernel.clone())
    };
    Ok(Linear {
        parameter_count: axes.len(),
        axes,
        candidates_empty: false,
        guard,
        particular,
        kernel,
        slots,
        action,
        offset,
        equations: matrix,
        rhs,
        fiber,
    })
}

fn apply(matrix: &Matrix, point: &[Z], c: &Control) -> Result<Vec<Z>, ValidationFailure> {
    matrix
        .iter()
        .map(|row| {
            if row.len() != point.len() {
                return Err("復元写像の寸法が違う".into());
            }
            let mut value = Z::zero();
            for (a, b) in row.iter().zip(point) {
                c.clone().checkpoint(Checkpoint::PrimitiveValuation)?;
                value += a * b;
            }
            Ok(value)
        })
        .collect()
}
fn compose(
    left: &Matrix,
    right: &Matrix,
    cols: usize,
    c: &Control,
) -> Result<Matrix, ValidationFailure> {
    let mut result = vec![vec![Z::zero(); cols]; left.len()];
    for (i, row) in left.iter().enumerate() {
        if row.len() != right.len() {
            return Err("整数写像の合成寸法が違う".into());
        }
        for (k, a) in row.iter().enumerate() {
            if right[k].len() != cols {
                return Err("整数写像の列数が違う".into());
            }
            for j in 0..cols {
                c.clone().checkpoint(Checkpoint::PrimitiveValuation)?;
                result[i][j] += a * &right[k][j];
            }
        }
    }
    Ok(result)
}

/// 許可作用の引数と独立な更新位置の座標を分け、方程式側の全自由状態を読む。
pub(in crate::observed) fn state_equations(
    env: &Environment<'_>,
    slots: &[Fact],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<(Matrix, Vec<Option<Z>>), ValidationFailure> {
    let assignments = env.fixed_values();
    let mut state = Environment::with_primitive_valuation(env.inputs, &assignments, &mut env.control.clone())?;
    state.object = env.object_domain();
    for slot in slots {
        env.tick()?;
        if env.field(&slot.snapshot, &slot.subject, slot.field.as_ref().ok_or("自由位置にfieldがない")?)?.ty.erase() != Type::Z {
            return Err("整数局所状態の自由位置がZでない".into());
        }
        state.affine_valuation.insert(slot.clone(), Form::state(slot, &env.control)?);
    }
    requirement_equations(&state, Axes::State(slots), requirements, missing)
}
fn requirement_equations(
    env: &Environment<'_>, axes: Axes<'_>,
    requirements: &[(String, Vec<(String, Scalar)>)], missing: &mut Pending,
) -> Result<(Matrix, Vec<Option<Z>>), ValidationFailure> {
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
        for (name, v) in bindings {
            let p = law_params.iter().find(|p| p.name == *name).ok_or("整数Lawの束縛名が異なる")?;
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
            return Err(unsupported(env, *body, "整数Lawの適用条件が未確定"));
        }
        let (vars, universal) = law_variables(env, law_params, bindings)?;
        missing.universal = universal;
        if let Some(guard) = guard {
            let v = env.scoped_ast(*guard, &vars, &Scope::default(), &law.reading)?;
            usable(env, *guard, &v)?;
            match v.known_value {
                Some(Scalar::Bool(false)) => continue,
                Some(Scalar::Bool(true)) => {}
                _ => {
                    return Err(unsupported(
                        env,
                        *guard,
                        "整数候補で変化するLaw guardの全解は未実装",
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
