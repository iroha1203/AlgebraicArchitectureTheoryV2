//! 元の有理parameter上で作用とLawを正規化し、完全な線形fiberを求める。
use super::change_affine::{Pending, capture_missing, with_missing};
use super::*;
use crate::observed::{
    affine::{self, Form, NumberType, Parameter},
    field_fiber::{self, Fiber, Matrix},
    field_polyhedron::{self, Halfspace, Outcome},
    numeric,
};
use archsig_input::law::model::{Declaration, Signature};
#[derive(Clone, Debug)]
pub(in crate::observed) struct Linear {
    pub parameter_count: usize,
    pub axes: Vec<Parameter>,
    pub guard_fiber: Fiber,
    pub slots: Vec<Fact>,
    pub action: Matrix,
    pub offset: Vec<Scalar>,
    pub equations: Matrix,
    pub rhs: Vec<Scalar>,
    pub solutions: Solutions,
}

#[derive(Clone, Debug)]
pub(in crate::observed) enum Solutions {
    Affine(Fiber),
    Polyhedron(Polyhedron),
}

#[derive(Clone, Debug)]
pub(in crate::observed) struct Polyhedron {
    pub inequalities: Vec<Halfspace>,
    pub outcome: Outcome,
}

#[derive(Default)]
struct Constraints {
    equalities: Matrix,
    rhs: Vec<Option<Scalar>>,
    inequalities: Option<Vec<Halfspace>>,
    quantified: bool,
}

impl Constraints {
    fn contradiction(&mut self, n: usize, env: &Environment<'_>) -> Result<(), ValidationFailure> {
        self.equalities
            .push(vec![numeric::zero(&Type::Q, &env.control)?; n]);
        self.rhs
            .push(Some(numeric::literal("1", &Type::Q, &env.control)?));
        Ok(())
    }
}
fn unsupported(env: &Environment<'_>, id: usize, feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law {
            span: env.indexes.inputs.law().exprs()[id].span,
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
        support: vec![].into(),
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
/// Observation-only coefficients can remain unknown during extraction. The
/// shape check supplies no value to a missing slot and proves no constraint.
fn potential_affine(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    reading: &str,
    axes: &[Parameter],
    observations: &mut BTreeSet<Fact>,
) -> Result<Option<bool>, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        let value = env.scoped_ast(id, vars, &Scope::default(), reading)?;
        if let Some(form) = value.affine.as_deref() {
            observations.extend(form.missing_facts());
            if form.awaiting_rational_observation(axes, &env.control)?
                || form.rational_coordinates(axes, &env.control)?.is_some()
            {
                return Ok(Some(form.varies_over(axes, &env.control)?));
            }
            return Ok(None);
        }
        let kind = &env.indexes.inputs.law().exprs()[id].kind;
        if let ExprKind::Group(body)
        | ExprKind::Unary {
            op: archsig_input::law::ast::UnOp::Neg,
            operand: body,
        } = kind
        {
            return potential_affine(env, *body, vars, reading, axes, observations);
        }
        if let ExprKind::Call { args, .. } = kind
            && let Some(declaration) = env.named_view(id)?
            && let Signature::View { params, body, .. } = &declaration.signature
        {
            let mut local = BTreeMap::new();
            for (parameter, arg) in params.iter().zip(args) {
                let value = env.scoped_ast(*arg, vars, &Scope::default(), reading)?;
                local.insert(parameter.name.clone(), value);
            }
            return potential_affine(env, *body, &local, &declaration.reading, axes, observations);
        }
        if let ExprKind::Let { name, value, body } = kind {
            let mut local = env.copy_variables(vars)?;
            let bound = env.scoped_ast(*value, vars, &Scope::default(), reading)?;
            local.insert(name.name.clone(), bound);
            return potential_affine(env, *body, &local, reading, axes, observations);
        }
        if let ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } = kind
        {
            let condition = env.scoped_ast(*cond, vars, &Scope::default(), reading)?;
            match condition.known_value.as_ref() {
                Some(Scalar::Bool(true)) => {
                    return potential_affine(env, *then_branch, vars, reading, axes, observations);
                }
                Some(Scalar::Bool(false)) => {
                    return potential_affine(env, *else_branch, vars, reading, axes, observations);
                }
                _ if observation_only(env, *cond, vars, reading, axes, &condition)? => {
                    let a = potential_affine(env, *then_branch, vars, reading, axes, observations)?;
                    let b = potential_affine(env, *else_branch, vars, reading, axes, observations)?;
                    return Ok(a.zip(b).map(|(a, b)| a || b));
                }
                _ => return Ok(None),
            }
        }
        let ExprKind::Binary {
            op: op @ (BinOp::Add | BinOp::Sub | BinOp::Mul),
            lhs,
            rhs,
        } = kind
        else {
            return Ok(None);
        };
        let a = potential_affine(env, *lhs, vars, reading, axes, observations)?;
        let b = potential_affine(env, *rhs, vars, reading, axes, observations)?;
        Ok(match (a, b) {
            (Some(true), Some(true)) if *op == BinOp::Mul => None,
            (Some(a), Some(b)) => Some(a || b),
            _ => None,
        })
    })
}

fn observation_only(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    reading: &str,
    axes: &[Parameter],
    value: &SourceValue,
) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        if value.known_value.is_some() || !value.scope.assignments && axes.is_empty() {
            return Ok(true);
        }
        let base = Scope::default();
        let law = env.indexes.inputs.law();
        let child = |id| {
            let value = env.scoped_ast(id, vars, &base, reading)?;
            observation_only(env, id, vars, reading, axes, &value)
        };
        match &law.exprs()[id].kind {
            ExprKind::Group(body)
            | ExprKind::Unary {
                op: archsig_input::law::ast::UnOp::Not,
                operand: body,
            } => child(*body),
            ExprKind::Binary {
                op: BinOp::And | BinOp::Or | BinOp::Implies,
                lhs,
                rhs,
            } => Ok(child(*lhs)? && child(*rhs)?),
            ExprKind::Binary {
                op: BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge,
                lhs,
                rhs,
            } if law.expr_type(*lhs) == Some(&Type::Q) && law.expr_type(*rhs) == Some(&Type::Q) => {
                let left = env.scoped_ast(*lhs, vars, &base, reading)?;
                let right = env.scoped_ast(*rhs, vars, &base, reading)?;
                let form = affine::binary(
                    BinOp::Sub,
                    left.affine.as_deref(),
                    right.affine.as_deref(),
                    &env.control,
                )?;
                if let Some(form) = form {
                    return Ok(form.awaiting_rational_observation(&[], &env.control)?
                        || form.rational_coordinates(&[], &env.control)?.is_some());
                }
                let mut observations = BTreeSet::new();
                Ok(
                    potential_affine(env, *lhs, vars, reading, axes, &mut observations)?
                        == Some(false)
                        && potential_affine(env, *rhs, vars, reading, axes, &mut observations)?
                            == Some(false),
                )
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let condition = env.scoped_ast(*cond, vars, &base, reading)?;
                match condition.known_value.as_ref() {
                    Some(Scalar::Bool(true)) => child(*then_branch),
                    Some(Scalar::Bool(false)) => child(*else_branch),
                    _ => Ok(
                        observation_only(env, *cond, vars, reading, axes, &condition)?
                            && child(*then_branch)?
                            && child(*else_branch)?,
                    ),
                }
            }
            ExprKind::Quant {
                split:
                    archsig_input::law::ast::QuantSplit::Fixed {
                        domain: archsig_input::law::ast::QuantDomain::In(_),
                        ..
                    },
                ..
            } => {
                let spec = quantifier::spec(law, id, &env.control)?;
                let (domain, members) =
                    env.scoped_quantifier_domain(&spec, vars, &base, reading)?;
                let Some(members) = members else {
                    let Some(id) = spec.domain else {
                        return Ok(false);
                    };
                    return observation_only(env, id, vars, reading, axes, &domain);
                };
                let mut local = env.copy_variables(vars)?;
                for member in members {
                    let bound = self::value(env, member)?;
                    local.insert(spec.name.into(), bound);
                    let body = env.scoped_ast(spec.body, &local, &base, reading)?;
                    if !observation_only(env, spec.body, &local, reading, axes, &body)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(!value.scope.assignments && !change_affine::numeric_condition(env, id, value)?),
        }
    })
}

// A read which cancels out of a comparison is not a required observation.
fn normalized_missing(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    reading: &str,
) -> Result<Option<Vec<Fact>>, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        let base = Scope::default();
        let source = env.scoped_ast(id, vars, &base, reading)?;
        if source.known_value.is_some() {
            return Ok(Some(vec![]));
        }
        let law = env.indexes.inputs.law();
        match &law.exprs()[id].kind {
            ExprKind::Group(body) => normalized_missing(env, *body, vars, reading),
            ExprKind::Binary {
                op: BinOp::And | BinOp::Or | BinOp::Implies,
                lhs,
                rhs,
            } => {
                let a = normalized_missing(env, *lhs, vars, reading)?;
                let b = normalized_missing(env, *rhs, vars, reading)?;
                Ok(a.zip(b).map(|(mut a, b)| {
                    a.extend(b);
                    a
                }))
            }
            ExprKind::Binary {
                op: BinOp::Eq | BinOp::Ne | BinOp::Le | BinOp::Lt | BinOp::Ge | BinOp::Gt,
                lhs,
                rhs,
            } if law.expr_type(*lhs) == Some(&Type::Q) && law.expr_type(*rhs) == Some(&Type::Q) => {
                let left = env.scoped_ast(*lhs, vars, &base, reading)?;
                let right = env.scoped_ast(*rhs, vars, &base, reading)?;
                Ok(affine::binary(
                    BinOp::Sub,
                    left.affine.as_deref(),
                    right.affine.as_deref(),
                    &env.control,
                )?
                .map(|difference| difference.missing_facts()))
            }
            _ => Ok(None),
        }
    })
}

fn equations(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    reading: &str,
    axes: Axes<'_>,
    rows: &mut Constraints,
    missing: &mut Pending,
) -> Result<(), ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        let base = Scope::default();
        let law = env.indexes.inputs.law();
        let kind = &law.exprs()[id].kind;
        let allow_bounds = rows.inequalities.is_some();
        let (v, absent) = if allow_bounds {
            capture_missing(env, || env.scoped_ast(id, vars, &base, reading))?
        } else {
            (env.scoped_ast(id, vars, &base, reading), vec![])
        };
        let v = v?;
        if !v.condition_pending
            && !v.condition_failed
            && let Some(Scalar::Bool(holds)) = v.known_value
        {
            if !holds {
                rows.contradiction(axes.len(), env)?;
            }
            return Ok(());
        }
        if allow_bounds
            && matches!(
                kind,
                ExprKind::Quant {
                    kind: archsig_input::law::ast::QuantKind::Forall,
                    split: archsig_input::law::ast::QuantSplit::Fixed {
                        domain: archsig_input::law::ast::QuantDomain::In(_),
                        ..
                    },
                    ..
                }
            )
        {
            let spec = quantifier::spec(law, id, &env.control)?;
            let domain = spec.domain.ok_or(internal!("有理量化の元域がない"))?;
            let (quantified, absent) = capture_missing(env, || {
                env.scoped_quantifier_domain(&spec, vars, &base, reading)
            })?;
            let (domain_value, members) = quantified?;
            let Some(members) = members else {
                let mut parameters = match axes {
                    Axes::Parameters(parameters) => parameters.to_vec(),
                    Axes::State(_) => vec![],
                };
                parameters.extend_from_slice(&missing.universal);
                missing.awaiting_observation = !absent.is_empty()
                    && observation_only(env, domain, vars, reading, &parameters, &domain_value)?;
                missing.facts.extend(absent);
                missing.unsupported = Some("rational_change_quantification");
                return Err(unsupported(env, domain, "有理changeの有限量化域が未確定"));
            };
            usable(env, domain, &domain_value)?;
            let mut local = env.copy_variables(vars)?;
            let enclosing = rows.quantified;
            rows.quantified = true;
            for member in members {
                env.tick()?;
                if member.ty() != spec.element {
                    return Err(internal!("有理量化の元要素型が異なる").into());
                }
                let mut v = value(env, member)?;
                v.scope = domain_value.scope.clone();
                v.scalar_scope = Some(domain_value.scope.clone());
                local.insert(spec.name.to_owned(), v);
                equations(env, spec.body, &local, reading, axes, rows, missing)?;
            }
            rows.quantified = enclosing;
            return Ok(());
        }

        missing.awaiting_observation = false;
        if !allow_bounds {
            usable(env, id, &v)?;
        }
        match kind {
            ExprKind::Group(body) => equations(env, *body, vars, reading, axes, rows, missing),
            ExprKind::Let { name, value, body } => {
                let mut vars = vars.clone();
                let v = env.scoped_ast(*value, &vars, &base, reading)?;
                usable(env, *value, &v)?;
                vars.insert(name.name.clone(), v);
                equations(env, *body, &vars, reading, axes, rows, missing)
            }
            ExprKind::Binary {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                equations(env, *lhs, vars, reading, axes, rows, missing)?;
                equations(env, *rhs, vars, reading, axes, rows, missing)
            }
            ExprKind::Binary {
                op: BinOp::Implies,
                lhs,
                rhs,
            } if allow_bounds => {
                let (guard, absent) =
                    capture_missing(env, || env.scoped_ast(*lhs, vars, &base, reading))?;
                let guard = guard?;
                match guard
                    .known_value
                    .as_ref()
                    .filter(|_| !guard.condition_pending && !guard.condition_failed)
                {
                    Some(Scalar::Bool(true)) => {
                        equations(env, *rhs, vars, reading, axes, rows, missing)
                    }
                    Some(Scalar::Bool(false)) => Ok(()),
                    _ => {
                        let mut parameters = match axes {
                            Axes::Parameters(parameters) => parameters.to_vec(),
                            Axes::State(_) => vec![],
                        };
                        parameters.extend_from_slice(&missing.universal);
                        missing.awaiting_observation = !absent.is_empty()
                            && observation_only(env, *lhs, vars, reading, &parameters, &guard)?;
                        missing.facts.extend(absent);
                        missing.unsupported = Some("rational_change_implication");
                        Err(unsupported(env, *lhs, "有理changeの含意の前件が未確定"))
                    }
                }
            }
            ExprKind::Quant { .. } => {
                missing.unsupported = Some("rational_change_quantification");
                Err(unsupported(
                    env,
                    id,
                    "有理changeで既知の有限In全称量化以外を線形系に展開する算法は未対応",
                ))
            }
            _ => {
                if v.condition_pending || v.condition_failed {
                    missing.awaiting_observation =
                        v.condition_pending && !absent.is_empty() && !v.scope.assignments;
                    missing.facts.extend(absent);
                    return usable(env, id, &v);
                }
                let ordered = match kind {
                    ExprKind::Binary {
                        op: BinOp::Le,
                        lhs,
                        rhs,
                    } if allow_bounds => Some((*lhs, *rhs)),
                    ExprKind::Binary {
                        op: BinOp::Ge,
                        lhs,
                        rhs,
                    } if allow_bounds => Some((*rhs, *lhs)),
                    _ => None,
                };
                let form = if let Some((lhs, rhs)) = ordered {
                    let left = env.scoped_ast(lhs, vars, &base, reading)?;
                    let right = env.scoped_ast(rhs, vars, &base, reading)?;
                    usable(env, lhs, &left)?;
                    usable(env, rhs, &right)?;
                    affine::binary(
                        BinOp::Sub,
                        left.affine.as_deref(),
                        right.affine.as_deref(),
                        &env.control,
                    )?
                } else if let Some(p) = v
                    .comparison
                    .as_ref()
                    .filter(|p| p.op == BinOp::Eq && p.bound_axes.is_empty())
                {
                    affine::binary(BinOp::Sub, Some(&p.left), Some(&p.right), &env.control)?
                } else {
                    None
                };
                let Some(form) = form else {
                    let q_comparison = match kind {
                        ExprKind::Binary {
                            op: BinOp::Eq | BinOp::Le | BinOp::Ge,
                            lhs,
                            rhs,
                        } if law.expr_type(*lhs) == Some(&Type::Q)
                            && law.expr_type(*rhs) == Some(&Type::Q) =>
                        {
                            Some((*lhs, *rhs))
                        }
                        _ => None,
                    };
                    if let Axes::Parameters(parameters) = axes
                        && let Some((lhs, rhs)) = q_comparison
                        && (rows.quantified || ordered.is_some())
                    {
                        let mut observations = BTreeSet::new();
                        let left = potential_affine(
                            env,
                            lhs,
                            vars,
                            reading,
                            parameters,
                            &mut observations,
                        )?;
                        let right = potential_affine(
                            env,
                            rhs,
                            vars,
                            reading,
                            parameters,
                            &mut observations,
                        )?;
                        missing.awaiting_observation = left.is_some()
                            && right.is_some()
                            && (!absent.is_empty() || !observations.is_empty());
                        missing.facts.extend(observations);
                    }
                    if change_affine::numeric_condition(env, id, &v)? {
                        missing.unsupported = Some("numeric_change_condition");
                    } else if !absent.is_empty()
                        && !v.scope.assignments
                        && missing.universal.is_empty()
                    {
                        missing.awaiting_observation = true;
                    }
                    if !absent.is_empty() {
                        missing
                            .facts
                            .extend(normalized_missing(env, id, vars, reading)?.unwrap_or(absent));
                    }
                    return Err(unsupported(
                        env,
                        id,
                        "有理changeの全解は既知係数のアフィン等式・対応する非狭義不等式の連言を要する",
                    ));
                };
                if form.varies_over(&missing.universal, &env.control)? {
                    rows.contradiction(axes.len(), env)?;
                    return Ok(());
                }
                if (ordered.is_some() || rows.quantified)
                    && let Axes::Parameters(parameters) = axes
                {
                    missing.awaiting_observation =
                        form.awaiting_rational_observation(parameters, &env.control)?;
                }
                let (constant, coefficients) = coordinates(env, id, &form, axes, missing)?;
                let rhs = constant
                    .as_ref()
                    .map(|c| numeric::unary(archsig_input::law::ast::UnOp::Neg, c, &env.control))
                    .transpose()?;
                if ordered.is_none() {
                    rows.equalities.push(coefficients);
                    rows.rhs.push(rhs);
                } else {
                    rows.inequalities
                        .as_mut()
                        .ok_or(internal!("有理局所等式に不等式がある"))?
                        .push(Halfspace {
                            coefficients,
                            rhs: rhs.ok_or(internal!("有理不等式の右辺が未確定"))?,
                        });
                }
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
        return Err(internal!("rational guard requires Q parameters").into());
    }
    let mut rows = Constraints::default();
    if let Some(id) = guard {
        missing.expression = Some(id);
        let value = env.scoped_ast(id, vars, &Scope::default(), reading)?;
        missing.support.extend(value.support.into_vec());
        missing.scope.merge(&value.scope);
        equations(
            env,
            id,
            vars,
            reading,
            Axes::Parameters(axes),
            &mut rows,
            missing,
        )?;
    }
    let rhs = rows
        .rhs
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or(internal!("rational guard constant is undetermined"))?;
    let fiber = field_fiber::solve(&Type::Q, &rows.equalities, axes.len(), &rhs, &env.control)?;
    Ok((rows.equalities, rhs, fiber))
}

pub(in crate::observed) fn compute(
    env: &Environment<'_>,
    change: &Declaration,
    subjects: &[Scalar],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<Linear, ValidationFailure> {
    with_missing(env, missing, |missing| {
        compute_inner(env, change, subjects, requirements, false, missing)
    })
}
pub(in crate::observed) fn compute_with_bounds(
    env: &Environment<'_>,
    change: &Declaration,
    subjects: &[Scalar],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<Linear, ValidationFailure> {
    with_missing(env, missing, |missing| {
        compute_inner(env, change, subjects, requirements, true, missing)
    })
}

fn compute_inner(
    env: &Environment<'_>,
    change: &Declaration,
    subjects: &[Scalar],
    requirements: &[(String, Vec<(String, Scalar)>)],
    allow_bounds: bool,
    missing: &mut Pending,
) -> Result<Linear, ValidationFailure> {
    missing.coefficient_type = Some(Type::Q);
    let Signature::Change {
        params,
        guard,
        body,
    } = &change.signature
    else {
        return Err(internal!("有理候補がchangeでない").into());
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
    let mut updates = BTreeMap::<Fact, (Form, Scalar, Vec<Scalar>)>::new();
    let mut guards = Constraints::default();
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
                &mut guards,
                missing,
            )?;
        }
        missing.expression = Some(*body);
        let mut current = *body;
        loop {
            env.tick()?;
            match &env.indexes.inputs.law().exprs()[current].kind {
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
                                missing.unsupported = Some("numeric_change_condition");
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
                            if matches!(env.indexes.inputs.law().expr_type(*id), Some(Type::Q)) {
                                missing.unsupported = Some("nonlinear_numeric_change");
                            }
                            unsupported(env, *id, "有理changeの更新式がQアフィンでない")
                        })?;
                        let position = Fact::from(archsig_input::archmap::FactData {
                            snapshot: snapshot.clone(),
                            subject: subject.clone(),
                            field: Some(env.input_name(&format!("{entity}.{}", field.name))?),
                            atom: None,
                        });
                        if let Some((prior, _, _)) = updates.get(&position) {
                            if prior != form.as_ref() {
                                return Err(unsupported(
                                    env,
                                    *id,
                                    "有理changeの同時更新衝突のfiberは未実装",
                                ));
                            }
                        } else {
                            let (constant, row) =
                                coordinates(env, *id, &form, Axes::Parameters(&axes), missing)?;
                            let constant = constant.ok_or(internal!("有理作用の固定項が未確定"))?;
                            updates.insert(position, (*form, constant, row));
                        }
                    }
                    break;
                }
                _ => return Err(internal!("有理changeのwithがない").into()),
            }
        }
    }
    let mut slots = vec![];
    let mut action = vec![];
    let mut offset = vec![];
    let mut valuation = BTreeMap::new();
    for (slot, (form, constant, row)) in updates {
        env.tick()?;
        slots.push(slot.clone());
        action.push(row);
        offset.push(constant);
        valuation.insert(slot, form);
    }

    let mut guard_matrix = guards.equalities;
    let mut guard_rhs = guards
        .rhs
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or(internal!("有理guardの固定項が未確定"))?;
    let guard_fiber = field_fiber::solve(
        &Type::Q,
        &guard_matrix,
        axes.len(),
        &guard_rhs,
        &env.control,
    )?;
    let candidates_empty = guard_fiber.particular.is_none();
    let mut updated = Environment::with_primitive_valuation(
        env.indexes.inputs,
        &env.fixed_values(),
        &env.control,
    )?;
    updated.indexes.object = env.object_domain();
    updated.indexes.affine_valuation = valuation;
    let rows = if candidates_empty {
        Constraints::default()
    } else {
        with_missing(&updated, missing, |missing| {
            requirement_equations(
                &updated,
                Axes::Parameters(&axes),
                requirements,
                allow_bounds,
                missing,
            )
        })?
    };
    guard_matrix.extend(rows.equalities);
    guard_rhs.extend(
        rows.rhs
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or(internal!("有理要求の固定項が未確定"))?,
    );
    let solutions = if let Some(inequalities) = rows.inequalities
        && !inequalities.is_empty()
    {
        let original =
            field_polyhedron::halfspaces(&guard_matrix, &guard_rhs, &inequalities, &env.control)?;
        let outcome = field_polyhedron::solve(&original, axes.len(), &env.control)?;
        Solutions::Polyhedron(Polyhedron {
            inequalities,
            outcome,
        })
    } else {
        Solutions::Affine(field_fiber::solve(
            &Type::Q,
            &guard_matrix,
            axes.len(),
            &guard_rhs,
            &env.control,
        )?)
    };
    Ok(Linear {
        parameter_count: axes.len(),
        axes,
        guard_fiber,
        slots,
        action,
        offset,
        equations: guard_matrix,
        rhs: guard_rhs,
        solutions,
    })
}
pub(in crate::observed) fn state_equations(
    env: &Environment<'_>,
    slots: &[Fact],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<(Matrix, Vec<Option<Scalar>>), ValidationFailure> {
    let mut state = Environment::with_primitive_valuation(
        env.indexes.inputs,
        &env.fixed_values(),
        &env.control,
    )?;
    state.indexes.object = env.object_domain();
    for slot in slots {
        env.tick()?;
        if env
            .indexes
            .field(
                &env.state,
                &slot.snapshot,
                &slot.subject,
                slot.field
                    .as_ref()
                    .ok_or(internal!("自由位置にfieldがない"))?,
            )?
            .ty
            .erase()
            != Type::Q
        {
            return Err(internal!("有理局所状態の自由位置がQでない").into());
        }
        state.indexes.affine_valuation.insert(
            slot.clone(),
            Form::typed_state(&Type::Q, slot, &env.control)?,
        );
    }
    with_missing(&state, missing, |missing| {
        let rows = requirement_equations(&state, Axes::State(slots), requirements, false, missing)?;
        Ok((rows.equalities, rows.rhs))
    })
}
fn requirement_equations(
    env: &Environment<'_>,
    axes: Axes<'_>,
    requirements: &[(String, Vec<(String, Scalar)>)],
    allow_bounds: bool,
    missing: &mut Pending,
) -> Result<Constraints, ValidationFailure> {
    let _value_read = allow_bounds.then(|| env.state.value_read.scoped(true));
    missing.selective_missing = allow_bounds;
    let mut rows = Constraints {
        inequalities: allow_bounds.then(Vec::new),
        ..Default::default()
    };
    for (name, bindings) in requirements {
        let law = &env.indexes.inputs.law().declarations()[name];
        let Signature::Law {
            body,
            guard,
            params: law_params,
            ..
        } = &law.signature
        else {
            return Err(internal!("有理候補の要求がLawでない").into());
        };
        let mut checked = BTreeMap::new();
        let mut checks = owned_call::Checks::default();
        for (name, v) in bindings {
            let p = law_params
                .iter()
                .find(|p| p.name == *name)
                .ok_or(internal!("有理Lawの束縛名が異なる"))?;
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
            missing.expression = Some(*body);
            missing.bindings = bindings.clone();
            missing.facts.extend(checks.missing);
            missing.awaiting_observation = !missing.facts.is_empty();
            return Err(unsupported(env, *body, "有理Lawの適用条件が未確定"));
        }
        let (vars, universal) = change_affine::law_variables(env, law_params, bindings)?;
        missing.universal = universal;
        if let Some(guard) = guard {
            let (v, absent) = if allow_bounds {
                capture_missing(env, || {
                    env.scoped_ast(*guard, &vars, &Scope::default(), &law.reading)
                })?
            } else {
                (
                    env.scoped_ast(*guard, &vars, &Scope::default(), &law.reading),
                    vec![],
                )
            };
            let v = v?;
            let mut parameters = match axes {
                Axes::Parameters(parameters) => parameters.to_vec(),
                Axes::State(_) => vec![],
            };
            parameters.extend_from_slice(&missing.universal);
            missing.awaiting_observation = !absent.is_empty()
                && observation_only(env, *guard, &vars, &law.reading, &parameters, &v)?;
            if v.condition_pending || v.condition_failed {
                missing.facts.extend(absent.iter().cloned());
            }
            usable(env, *guard, &v)?;
            match v.known_value {
                Some(Scalar::Bool(false)) => continue,
                Some(Scalar::Bool(true)) => {}
                _ => {
                    missing.expression = Some(*guard);
                    missing.bindings = bindings.clone();
                    missing.parameters = law_params
                        .iter()
                        .filter(|p| !bindings.iter().any(|(name, _)| *name == p.name))
                        .map(|p| (p.name.clone(), p.ty.clone()))
                        .collect();
                    missing.facts.extend(absent);
                    if change_affine::numeric_condition(env, *guard, &v)? {
                        missing.unsupported = Some("numeric_change_condition");
                    }
                    return Err(unsupported(
                        env,
                        *guard,
                        "有理候補で未確定のLaw guardの全解は未実装",
                    ));
                }
            }
        }
        missing.awaiting_observation = false;
        missing.expression = Some(*body);
        missing.bindings = bindings.clone();
        missing.parameters = law_params
            .iter()
            .filter(|p| !bindings.iter().any(|(n, _)| *n == p.name))
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect();
        equations(env, *body, &vars, &law.reading, axes, &mut rows, missing)?;
    }
    Ok(rows)
}
