//! 通常の式評価器から整数changeの作用と選択Lawの線形系を得る。
use super::*;
use crate::observed::environment::state::ScopedReplace;
use crate::observed::{
    affine::{self, Form, NumberType, Parameter},
    integer_fiber::{self, Fiber, Matrix},
};
use archsig_input::law::model::{Declaration, Signature};
use num_bigint::BigInt as Z;
use num_traits::{One, Zero};

#[derive(Clone, Debug, PartialEq, Eq)]
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
    pub support: Vec<Fact>,
    pub scope: Scope,
    pub universal: Vec<Parameter>,
    pub coefficient_type: Option<Type>,
    pub unsupported: Option<&'static str>,
    pub facts: Vec<Fact>,
    pub expression: Option<usize>,
    pub bindings: Vec<(String, Scalar)>,
    pub parameters: Vec<(String, Type)>,
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
        support: vec![],
        scalar_scope: Some(Scope::default()),
    })
}
/// 未束縛の数値Law引数は標本値ではなく、元binderの全域記号として評価する。
pub(super) fn law_variables(
    env: &Environment<'_>,
    params: &[archsig_input::law::model::Param],
    bindings: &[(String, Scalar)],
) -> Result<(BTreeMap<String, SourceValue>, Vec<Parameter>), ValidationFailure> {
    let mut names = std::collections::BTreeSet::new();
    for (name, scalar) in bindings {
        env.tick()?;
        if !names.insert(name)
            || !params
                .iter()
                .any(|p| p.name == *name && p.ty.erase() == scalar.ty())
        {
            return Err(internal!("Law束縛の名前・型または重複が不正").into());
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
                Type::Z => NumberType::Z,
                Type::Q => NumberType::Q,
                _ => return Err(internal!("未束縛の局所Law引数がZ/Qでない").into()),
            };
            let parameter = Parameter {
                binder: p.span,
                name: p.name.clone(),
                context: env.state.context.get().unwrap_or_default(),
                kind,
            };
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
/// 通常Evaluatorの束縛で、アフィン等式の連言を元の行列式へ分解する。
/// 非対応の論理式は部分的な連立系として受け入れない。
pub(super) fn guard_forms(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    base: &Scope,
    reading: &str,
) -> Result<Option<Vec<Form>>, ValidationFailure> {
    Ok(super::numeric_guard::analyze(env, id, vars, base, reading)?.forms)
}
pub(super) fn affine_guard_forms(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    base: &Scope,
    reading: &str,
) -> Result<Option<Vec<Form>>, ValidationFailure> {
    super::conjunction::walk(&mut AffineGuard, env, id, vars, base, reading)
}

#[derive(Clone, Copy)]
enum Axes<'a> {
    Parameters(&'a [Parameter]),
    State(&'a [Fact]),
}
impl Axes<'_> {
    fn len(self) -> usize {
        match self {
            Self::Parameters(xs) => xs.len(),
            Self::State(xs) => xs.len(),
        }
    }
}
fn coordinates(
    env: &Environment<'_>,
    id: usize,
    form: &Form,
    axes: Axes<'_>,
    missing: &mut Pending,
) -> Result<(Option<Z>, Vec<Z>), ValidationFailure> {
    (match axes {
        Axes::Parameters(xs) => form
            .integer_coordinates(xs, &env.control)?
            .map(|(v, row)| (Some(v), row)),
        Axes::State(xs) => {
            missing.facts.extend(form.missing_facts());
            form.state_coordinates(xs, &env.control)?
        }
    })
    .ok_or_else(|| {
        missing.facts.extend(form.missing_facts());
        unsupported(
            env,
            id,
            "整数changeの係数に欠測または元parameter以外の記号がある",
        )
    })
}
pub(super) fn numeric_condition(
    env: &Environment<'_>,
    mut id: usize,
    value: &SourceValue,
) -> Result<bool, ValidationFailure> {
    if value.comparison.is_some() {
        return Ok(true);
    }
    loop {
        env.tick()?;
        match &env.indexes.inputs.law().exprs()[id].kind {
            ExprKind::Group(body) | ExprKind::Let { body, .. } => id = *body,
            ExprKind::Binary { lhs, rhs, .. } => {
                return Ok([lhs, rhs].iter().all(|id| {
                    matches!(
                        env.indexes.inputs.law().expr_type(**id),
                        Some(Type::Z | Type::Q)
                    )
                }));
            }
            _ => return Ok(false),
        }
    }
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
    super::conjunction::walk(
        &mut IntegerEquations {
            axes,
            matrix,
            rhs,
            missing,
        },
        env,
        id,
        vars,
        &Scope::default(),
        reading,
    )
}

struct AffineGuard;
impl super::conjunction::Interpretation for AffineGuard {
    type Output = Option<Vec<Form>>;
    fn value(
        &mut self,
        env: &Environment<'_>,
        _id: usize,
        _vars: &BTreeMap<String, SourceValue>,
        _reading: &str,
        value: &SourceValue,
    ) -> Result<Option<Self::Output>, ValidationFailure> {
        if value.condition_failed || value.condition_pending {
            return Ok(Some(None));
        }
        if let Some(Scalar::Bool(holds)) = value.known_value {
            return Ok(Some(Some(if holds {
                vec![]
            } else {
                vec![
                    affine::constant(&Scalar::Z(Z::one()), &env.control)?
                        .ok_or(internal!("偽guardの数値定数がない"))?,
                ]
            })));
        }
        if let Some(comparison) = value
            .comparison
            .as_ref()
            .filter(|p| p.op == BinOp::Eq && p.bound_axes.is_empty())
        {
            return Ok(Some(
                affine::binary(
                    BinOp::Sub,
                    Some(&comparison.left),
                    Some(&comparison.right),
                    &env.control,
                )?
                .map(|form| vec![form]),
            ));
        }
        Ok(None)
    }
    fn bind(
        &mut self,
        env: &Environment<'_>,
        value: usize,
        name: &str,
        vars: &BTreeMap<String, SourceValue>,
        base: &Scope,
        reading: &str,
    ) -> Result<Option<BTreeMap<String, SourceValue>>, ValidationFailure> {
        let value = env.scoped_ast(value, vars, base, reading)?;
        if value.condition_failed || value.condition_pending {
            return Ok(None);
        }
        let mut vars = vars.clone();
        vars.insert(name.into(), value);
        Ok(Some(vars))
    }
    fn unavailable(&self) -> Self::Output {
        None
    }
    fn combine(&self, left: Self::Output, right: Self::Output) -> Self::Output {
        match (left, right) {
            (Some(mut left), Some(right)) => {
                left.extend(right);
                Some(left)
            }
            _ => None,
        }
    }
    fn leaf(
        &mut self,
        _env: &Environment<'_>,
        _id: usize,
        _value: &SourceValue,
    ) -> Result<Self::Output, ValidationFailure> {
        Ok(None)
    }
}
struct IntegerEquations<'a> {
    axes: Axes<'a>,
    matrix: &'a mut Matrix,
    rhs: &'a mut Vec<Option<Z>>,
    missing: &'a mut Pending,
}
impl super::conjunction::Interpretation for IntegerEquations<'_> {
    type Output = ();
    fn value(
        &mut self,
        env: &Environment<'_>,
        id: usize,
        vars: &BTreeMap<String, SourceValue>,
        reading: &str,
        v: &SourceValue,
    ) -> Result<Option<()>, ValidationFailure> {
        self.missing.support.extend(v.support.iter().cloned());
        self.missing.scope.merge(&v.scope);
        usable(env, id, v)?;
        if let Some(Scalar::Bool(holds)) = v.known_value {
            if !holds {
                self.matrix.push(vec![Z::zero(); self.axes.len()]);
                self.rhs.push(Some(Z::one()));
            }
            return Ok(Some(()));
        }
        if let ExprKind::Binary {
            op: BinOp::Eq,
            lhs,
            rhs,
        } = env.indexes.inputs.law().exprs()[id].kind
            && let Some(ty @ Type::Tuple(_)) = env.indexes.inputs.law().expr_type(lhs)
            && numeric::is_numeric_type(ty, &env.control)?
        {
            let difference = super::super::term::affine::operation(
                BinOp::Sub,
                &env.symbolic_source(lhs, vars, &v.scope, reading)?,
                &env.symbolic_source(rhs, vars, &v.scope, reading)?,
                ty,
                env.indexes.inputs.law(),
                env.indexes.inputs.law().exprs()[id].span,
                &env.control,
            )?;
            if let Some(forms) = tuple_forms(env, &difference)? {
                for form in forms {
                    self.add_form(env, id, &form)?;
                }
                return Ok(Some(()));
            }
        }
        if v.comparison.is_none()
            && let Some(forms) =
                parameter_coefficient_forms(env, id, vars, reading, &self.missing.universal)?
        {
            for form in forms {
                let (constant, coefficients) =
                    coordinates(env, id, &form, self.axes, self.missing)?;
                self.matrix.push(coefficients);
                self.rhs.push(constant.map(|v| -v));
            }
            return Ok(Some(()));
        }
        Ok(None)
    }
    fn bind(
        &mut self,
        env: &Environment<'_>,
        value: usize,
        name: &str,
        vars: &BTreeMap<String, SourceValue>,
        base: &Scope,
        reading: &str,
    ) -> Result<Option<BTreeMap<String, SourceValue>>, ValidationFailure> {
        let mut vars = vars.clone();
        let v = env.scoped_ast(value, &vars, base, reading)?;
        usable(env, value, &v)?;
        vars.insert(name.into(), v);
        Ok(Some(vars))
    }
    fn unavailable(&self) {}
    fn combine(&self, _left: (), _right: ()) {}
    fn leaf(
        &mut self,
        env: &Environment<'_>,
        id: usize,
        v: &SourceValue,
    ) -> Result<(), ValidationFailure> {
        let Some(p) = v
            .comparison
            .as_ref()
            .filter(|p| p.op == BinOp::Eq && p.bound_axes.is_empty())
        else {
            if numeric_condition(env, id, v)? {
                self.missing.unsupported = Some("numeric_change_condition");
            }
            return Err(unsupported(
                env,
                id,
                "整数changeの全解は既知係数のアフィン等式の連言を要する",
            ));
        };
        let form = affine::binary(BinOp::Sub, Some(&p.left), Some(&p.right), &env.control)?
            .ok_or(internal!("整数等式の差がない"))?;
        self.add_form(env, id, &form)
    }
}
impl IntegerEquations<'_> {
    fn add_form(
        &mut self,
        env: &Environment<'_>,
        id: usize,
        form: &Form,
    ) -> Result<(), ValidationFailure> {
        if form.varies_over(&self.missing.universal, &env.control)? {
            self.matrix.push(vec![Z::zero(); self.axes.len()]);
            self.rhs.push(Some(Z::one()));
            return Ok(());
        }
        let (constant, coefficients) = coordinates(env, id, &form, self.axes, self.missing)?;
        self.matrix.push(coefficients);
        self.rhs.push(constant.map(|v| -v));
        Ok(())
    }
}

fn tuple_forms(
    env: &Environment<'_>,
    value: &super::super::term::affine::Value,
) -> Result<Option<Vec<Form>>, ValidationFailure> {
    use super::super::term::affine::Value;
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        match value {
            Value::Number(form) => Ok(Some(vec![form.clone()])),
            Value::Known(Scalar::Tuple(items)) => {
                let mut forms = vec![];
                for item in items {
                    let Some(next) = tuple_forms(env, &Value::Known(item.clone()))? else {
                        return Ok(None);
                    };
                    forms.extend(next);
                }
                Ok(Some(forms))
            }
            Value::Known(value) => {
                Ok(affine::constant(value, &env.control)?.map(|form| vec![form]))
            }
            Value::Tuple(items) => {
                let mut forms = vec![];
                for item in items {
                    let Some(next) = tuple_forms(env, item)? else {
                        return Ok(None);
                    };
                    forms.extend(next);
                }
                Ok(Some(forms))
            }
            _ => Ok(None),
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
    let Some((ring, families, local_parameters)) =
        crate::observed::object_equation_presentation::parameter_differences_with_bindings(
            env.indexes.inputs,
            id,
            &Type::Z,
            env.state.context.get().unwrap_or_default(),
            &values,
            &parameters,
            &env.control,
        )
        .map_err(|cause| match cause {
            crate::construction::ConstructionFailure::Stopped(stop) => {
                ValidationFailure::Stop(stop)
            }
            crate::construction::ConstructionFailure::InvalidSelection(message) => {
                internal!(format!("数値Law係数: {message}")).into()
            }
            crate::construction::ConstructionFailure::Inconsistent(message) => message
                .with_message(format!("数値Law係数: {message}"))
                .into(),
        })?
    else {
        return Ok(None);
    };
    if ring.ty != Type::Z
        || families
            .iter()
            .flat_map(|family| &family.parameters)
            .any(|(p, _)| !universal.contains(p) && !local_parameters.contains(p))
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
        let subject = env.indexes.subject(&slot.snapshot, &slot.subject)?;
        if slot.field.owner() != Some(subject.ty.as_str()) {
            return Err(internal!("係数のfieldが元subject型と違う").into());
        }
        let base = value(
            env,
            Scalar::Subject {
                snapshot: slot.snapshot.clone(),
                subject: slot.subject.clone(),
                entity: subject.ty.to_string(),
            },
        )?;
        let source = env.scoped_field(
            base,
            &slot.field,
            &Scope::default(),
            reading,
            env.indexes.inputs.law().exprs()[id].span,
        )?;
        usable(env, id, &source)?;
        let Some(form) = source.affine else {
            return Ok(None);
        };
        fields.push(*form);
    }
    let mut forms = vec![];
    for coefficient in families.iter().flat_map(|family| {
        std::iter::once(&family.constant).chain(family.parameters.iter().map(|(_, p)| p))
    }) {
        env.tick()?;
        if coefficient.terms.is_empty() {
            continue;
        }
        let mut sum = affine::constant(&Scalar::Z(Z::zero()), &env.control)?
            .ok_or(internal!("係数の零がZでない"))?;
        for term in &coefficient.terms {
            env.tick()?;
            let Some(mut product) = affine::constant(term.coefficient.scalar(), &env.control)?
            else {
                return Ok(None);
            };
            for &variable in &term.variables {
                let field = fields
                    .get(variable)
                    .ok_or(internal!("係数の記号が範囲外"))?;
                let Some(next) =
                    affine::binary(BinOp::Mul, Some(&product), Some(field), &env.control)?
                else {
                    return Ok(None);
                };
                product = next;
            }
            sum = affine::binary(BinOp::Add, Some(&sum), Some(&product), &env.control)?
                .ok_or(internal!("係数の和がない"))?;
        }
        forms.push(sum);
    }
    Ok(Some(forms))
}
/// 更新値を読む前に、元guardが許す整数parameterの全fiberを構成する。
pub(in crate::observed) fn guard_domain(
    env: &Environment<'_>,
    change: &Declaration,
    subject: &Scalar,
    missing: &mut Pending,
) -> Result<Guard, ValidationFailure> {
    let Signature::Change { params, guard, .. } = &change.signature else {
        return Err(internal!("guardの元宣言がchangeでない").into());
    };
    let first = params.first().ok_or(internal!("changeの第1引数がない"))?;
    let (vars, axes) = law_variables(env, params, &[(first.name.clone(), subject.clone())])?;
    parameter_guard_domain(env, *guard, &vars, &axes, &change.reading, missing)
}
/// 既存の整数等式guardを、元parameter座標の全解として読む。
pub(super) fn parameter_guard_domain(
    env: &Environment<'_>,
    guard: Option<usize>,
    vars: &BTreeMap<String, SourceValue>,
    axes: &[Parameter],
    reading: &str,
    missing: &mut Pending,
) -> Result<Guard, ValidationFailure> {
    if axes.iter().any(|axis| axis.kind != NumberType::Z) {
        return Err(internal!("整数guardのparameter型が違う").into());
    }
    let mut matrix = vec![];
    let mut rhs = vec![];
    if let Some(id) = guard {
        missing.expression = Some(id);
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
        .ok_or(internal!("guard固定項が未確定"))?;
    let fiber = integer_fiber::solve(&matrix, axes.len(), &rhs, &env.control)?;
    Ok(Guard {
        equations: matrix,
        rhs,
        fiber,
    })
}
fn collect_updates(
    env: &Environment<'_>,
    body: usize,
    reading: &str,
    vars: &mut BTreeMap<String, SourceValue>,
    axes: &[Parameter],
    missing: &mut Pending,
    selected: Option<&str>,
    updates: &mut BTreeMap<Fact, Form>,
) -> Result<(), ValidationFailure> {
    let mut current = body;
    loop {
        env.tick()?;
        match &env.indexes.inputs.law().exprs()[current].kind {
            ExprKind::Group(inner) => current = *inner,
            ExprKind::Let { name, value, body } => {
                let v = env.scoped_ast(*value, vars, &Scope::default(), reading)?;
                missing.support.extend(v.support.iter().cloned());
                missing.scope.merge(&v.scope);
                usable(env, *value, &v)?;
                vars.insert(name.name.clone(), v);
                current = *body;
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let v = env.scoped_ast(*cond, vars, &Scope::default(), reading)?;
                missing.support.extend(v.support.iter().cloned());
                missing.scope.merge(&v.scope);
                usable(env, *cond, &v)?;
                current = match v.known_value {
                    Some(Scalar::Bool(true)) => *then_branch,
                    Some(Scalar::Bool(false)) => *else_branch,
                    _ => {
                        missing.expression = Some(*cond);
                        if numeric_condition(env, *cond, &v)? {
                            missing.unsupported = Some("numeric_change_condition");
                        }
                        return Err(unsupported(
                            env,
                            *cond,
                            "数値changeのparameter依存分岐は未実装",
                        ));
                    }
                };
            }
            ExprKind::With {
                base,
                updates: fields,
            } => {
                let target = env.scoped_ast(*base, vars, &Scope::default(), reading)?;
                missing.support.extend(target.support.iter().cloned());
                missing.scope.merge(&target.scope);
                usable(env, *base, &target)?;
                let Some(Scalar::Subject {
                    snapshot,
                    subject,
                    entity,
                }) = &target.known_value
                else {
                    return Err(unsupported(env, *base, "数値changeの更新先が未確定"));
                };
                for (field, id) in fields {
                    if selected.is_some_and(|name| name != field.name) {
                        continue;
                    }
                    let v = env.scoped_ast(*id, vars, &Scope::default(), reading)?;
                    missing.support.extend(v.support.iter().cloned());
                    missing.scope.merge(&v.scope);
                    usable(env, *id, &v)?;
                    let form = v.affine.ok_or_else(|| {
                        if matches!(
                            env.indexes.inputs.law().expr_type(*id),
                            Some(Type::Z | Type::Q)
                        ) {
                            missing.unsupported = Some("nonlinear_numeric_change");
                        }
                        unsupported(env, *id, "数値changeの更新式がアフィンでない")
                    })?;
                    if axes.first().is_some_and(|axis| axis.kind == NumberType::Q) {
                        form.rational_coordinates(axes, &env.control)?
                            .ok_or_else(|| {
                                missing.facts.extend(form.missing_facts());
                                unsupported(
                                    env,
                                    *id,
                                    "有理changeの係数に欠測または元parameter以外の記号がある",
                                )
                            })?;
                    } else {
                        coordinates(env, *id, &form, Axes::Parameters(axes), missing)?;
                    }
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
                                "数値changeの同時更新衝突のfiberは未実装",
                            ));
                        }
                    } else {
                        updates.insert(position, *form);
                    }
                }
                break;
            }
            _ => return Err(internal!("数値changeのwithがない").into()),
        }
    }
    Ok(())
}
/// guard域の確認後、選択した更新値のZ/Q係数と固定項を取り出す。
pub(in crate::observed) fn compute_update(
    env: &Environment<'_>,
    change: &Declaration,
    subject: &Scalar,
    field: &str,
    missing: &mut Pending,
) -> Result<(Vec<Scalar>, Scalar), ValidationFailure> {
    let Signature::Change { params, body, .. } = &change.signature else {
        return Err(internal!("整数候補がchangeでない").into());
    };
    let ty = params
        .get(1)
        .and_then(|p| numeric_parameters::coefficient_type(&p.ty));
    if ty.is_none()
        || params[1..]
            .iter()
            .any(|p| numeric_parameters::coefficient_type(&p.ty) != ty)
    {
        return Err(unsupported(
            env,
            *body,
            "数値changeの混合parameter型は未実装",
        ));
    }
    let ty = ty.ok_or(internal!("数値changeの係数型がない"))?;
    let bindings = vec![(params[0].name.clone(), subject.clone())];
    let (mut vars, axes) = numeric_parameters::law_variables(env, params, &bindings)?;
    missing.bindings = bindings;
    missing.parameters = params[1..]
        .iter()
        .map(|p| (p.name.clone(), p.ty.clone()))
        .collect();
    missing.expression = Some(*body);
    let mut updates = BTreeMap::new();
    with_missing(env, missing, |missing| {
        collect_updates(
            env,
            *body,
            &change.reading,
            &mut vars,
            &axes,
            missing,
            Some(field),
            &mut updates,
        )
    })?;
    let form = if let Some(form) = updates.into_values().next() {
        form
    } else {
        // The selected coordinate is unchanged by the original simultaneous update.
        let source = env.scoped_field(
            value(env, subject.clone())?,
            &env.input_name(&format!(
                "{}.{}",
                params[0]
                    .ty
                    .ref_target()
                    .ok_or(internal!("更新対象型がRefでない"))?,
                field
            ))?,
            &Scope::default(),
            &change.reading,
            change.span,
        )?;
        missing.support.extend(source.support.iter().cloned());
        missing.scope.merge(&source.scope);
        usable(env, *body, &source)?;
        *source
            .affine
            .ok_or_else(|| unsupported(env, *body, "数値changeの未更新値がアフィンでない"))?
    };
    let coordinates = match ty {
        Type::Z => form
            .integer_coordinates(&axes, &env.control)?
            .map(|(value, row)| (Scalar::Z(value), row.into_iter().map(Scalar::Z).collect())),
        Type::Q => form.rational_coordinates(&axes, &env.control)?,
        _ => return Err(internal!("数値changeの係数型が違う").into()),
    };
    let (constant, row) = coordinates.ok_or_else(|| {
        missing.facts.extend(form.missing_facts());
        unsupported(
            env,
            *body,
            "数値changeの係数に欠測または元parameter以外の記号がある",
        )
    })?;
    Ok((row, constant))
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
        return Err(internal!("整数候補がchangeでない").into());
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
        collect_updates(
            env,
            *body,
            &change.reading,
            &mut vars,
            &axes,
            missing,
            None,
            &mut updates,
        )?;
    }
    let mut slots = vec![];
    let mut action = vec![];
    let mut offset = vec![];
    for (slot, form) in &updates {
        let (constant, row) = coordinates(env, *body, form, Axes::Parameters(&axes), missing)?;
        slots.push(slot.clone());
        action.push(row);
        offset.push(constant.ok_or(internal!("作用の固定項が未確定"))?);
    }
    let guard_rhs = guard_rhs
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or(internal!("guardの固定項が未確定"))?;
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
        .indexes
        .primitive_valuation
        .as_ref()
        .map(|v| {
            v.iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let mut updated =
        Environment::with_primitive_valuation(env.indexes.inputs, &assignments, &env.control)?;
    updated.indexes.object = env.object_domain();
    updated.indexes.affine_valuation = updates;
    let (mut matrix, rhs) =
        requirement_equations(&updated, Axes::Parameters(&axes), requirements, missing)?;
    let mut rhs = rhs
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or(internal!("parameter方程式の固定項が未確定"))?;
    let free_count = guard
        .as_ref()
        .map_or(axes.len(), |g| axes.len() - g.fiber.rank);
    if let Some(g) = &guard {
        let origin = g
            .fiber
            .particular
            .as_ref()
            .ok_or(internal!("guardの特解がない"))?;
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
                for (value, offset) in restored.iter_mut().zip(
                    g.fiber
                        .particular
                        .as_ref()
                        .ok_or(internal!("guardの特解がない"))?,
                ) {
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
                return Err(internal!("復元写像の寸法が違う").into());
            }
            let mut value = Z::zero();
            for (a, b) in row.iter().zip(point) {
                c.checkpoint(Checkpoint::PrimitiveValuation)?;
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
            return Err(internal!("整数写像の合成寸法が違う").into());
        }
        for (k, a) in row.iter().enumerate() {
            if right[k].len() != cols {
                return Err(internal!("整数写像の列数が違う").into());
            }
            for j in 0..cols {
                c.checkpoint(Checkpoint::PrimitiveValuation)?;
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
    let mut state =
        Environment::with_primitive_valuation(env.indexes.inputs, &assignments, &env.control)?;
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
            != Type::Z
        {
            return Err(internal!("整数局所状態の自由位置がZでない").into());
        }
        state
            .indexes
            .affine_valuation
            .insert(slot.clone(), Form::state(slot, &env.control)?);
    }
    requirement_equations(&state, Axes::State(slots), requirements, missing)
}
fn requirement_equations(
    env: &Environment<'_>,
    axes: Axes<'_>,
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<(Matrix, Vec<Option<Z>>), ValidationFailure> {
    let mut matrix = vec![];
    let mut rhs = vec![];
    for (name, bindings) in requirements {
        let law = &env.indexes.inputs.law().declarations()[name];
        let Signature::Law {
            body,
            guard,
            params: law_params,
            ..
        } = &law.signature
        else {
            return Err(internal!("整数候補の要求がLawでない").into());
        };
        let mut checked = BTreeMap::new();
        let mut checks = owned_call::Checks::default();
        for (name, v) in bindings {
            let p = law_params
                .iter()
                .find(|p| p.name == *name)
                .ok_or(internal!("整数Lawの束縛名が異なる"))?;
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
                    missing.expression = Some(*guard);
                    missing.bindings = bindings.clone();
                    missing.parameters = law_params
                        .iter()
                        .filter(|p| !bindings.iter().any(|(name, _)| *name == p.name))
                        .map(|p| (p.name.clone(), p.ty.clone()))
                        .collect();
                    if numeric_condition(env, *guard, &v)? {
                        missing.unsupported = Some("numeric_change_condition");
                    }
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
        missing.parameters = law_params
            .iter()
            .filter(|p| !bindings.iter().any(|(n, _)| *n == p.name))
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect();
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

// Only the already constructed Z or Q fiber is normalized to scalar coordinates.
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct NumericGuard {
    pub(in crate::observed) equations: Vec<Vec<Scalar>>,
    pub(in crate::observed) rhs: Vec<Scalar>,
    pub(in crate::observed) particular: Option<Vec<Scalar>>,
    pub(in crate::observed) kernel: Vec<Vec<Scalar>>,
    rank: usize,
}
pub(super) fn numeric_guard_domain(
    env: &Environment<'_>,
    guard: Option<usize>,
    vars: &BTreeMap<String, SourceValue>,
    axes: &[crate::observed::affine::Parameter],
    reading: &str,
    pending: &mut Pending,
    ty: &Type,
) -> Result<NumericGuard, ValidationFailure> {
    with_missing(env, pending, |pending| match ty {
        Type::Z => {
            let guard = parameter_guard_domain(env, guard, vars, axes, reading, pending)?;
            let scalars = |row: Vec<num_bigint::BigInt>| -> Result<Vec<Scalar>, ValidationFailure> {
                row.into_iter()
                    .map(|value| {
                        env.tick()?;
                        Ok(Scalar::Z(value))
                    })
                    .collect()
            };
            Ok(NumericGuard {
                equations: guard
                    .equations
                    .into_iter()
                    .map(&scalars)
                    .collect::<Result<_, _>>()?,
                rhs: scalars(guard.rhs)?,
                particular: guard.fiber.particular.map(&scalars).transpose()?,
                kernel: guard
                    .fiber
                    .kernel
                    .into_iter()
                    .map(&scalars)
                    .collect::<Result<_, _>>()?,
                rank: guard.fiber.rank,
            })
        }
        Type::Q => {
            let (equations, rhs, fiber) = super::field_change::parameter_guard_domain(
                env, guard, vars, axes, reading, pending,
            )?;
            Ok(NumericGuard {
                equations,
                rhs,
                particular: fiber.particular,
                kernel: fiber.kernel,
                rank: fiber.pivots.len(),
            })
        }
        _ => Err(internal!("unsupported guard coefficient type").into()),
    })
}

// 通常評価器とcacheが既に保持する実読取りを使い、式形ごとの再走査を行わない。
pub(super) fn with_missing<T>(
    env: &Environment<'_>,
    missing: &mut Pending,
    operation: impl FnOnce(&mut Pending) -> Result<T, ValidationFailure>,
) -> Result<T, ValidationFailure> {
    let (result, reads) = capture_missing(env, || operation(missing))?;
    if result.is_err() {
        missing.facts.extend(reads);
    }
    result
}

pub(super) fn capture_missing<T>(
    env: &Environment<'_>,
    operation: impl FnOnce() -> T,
) -> Result<(T, Vec<Fact>), ValidationFailure> {
    let outer = env.state.missing_slot_reads.scoped(Some(BTreeSet::new()));
    let result = operation();
    let reads = outer
        .restore()
        .ok_or(internal!("数値式の不足位置収集がない"))?;
    if let Some(outer) = env.state.missing_slot_reads.borrow_mut().as_mut() {
        outer.extend(reads.iter().cloned());
    }
    Ok((
        result,
        reads
            .into_iter()
            .filter(|fact| {
                !env.indexes
                    .primitive_valuation
                    .as_ref()
                    .is_some_and(|values| values.contains_key(fact))
                    && !env.indexes.affine_valuation.contains_key(fact)
            })
            .collect(),
    ))
}

impl NumericGuard {
    // On the solver's full p + K R^d, a linear form is determined by p and K.
    pub(in crate::observed) fn violation(
        &self,
        row: &[Scalar],
        rhs: &Scalar,
        env: &Environment<'_>,
    ) -> Result<Option<Vec<Scalar>>, ValidationFailure> {
        let Some(origin) = &self.particular else {
            return Ok(None);
        };
        if row.len() != origin.len() {
            return Err(internal!("数値parameterの次元が違う").into());
        }
        let zero = numeric::zero(&rhs.ty(), &env.control)?;
        let dot = |point: &[Scalar]| -> Result<Scalar, ValidationFailure> {
            let mut value = zero.clone();
            for (a, x) in row.iter().zip(point) {
                env.tick()?;
                let product = numeric::binary(BinOp::Mul, a, x, &env.control)?;
                value = numeric::binary(BinOp::Add, &value, &product, &env.control)?;
            }
            Ok(value)
        };
        if dot(origin)? != *rhs {
            return Ok(Some(origin.clone()));
        }
        for column in 0..origin.len() - self.rank {
            let direction = self
                .kernel
                .iter()
                .map(|r| r[column].clone())
                .collect::<Vec<_>>();
            if dot(&direction)? != zero {
                return origin
                    .iter()
                    .zip(direction)
                    .map(|(a, b)| {
                        env.tick()?;
                        numeric::binary(BinOp::Add, a, &b, &env.control)
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map(Some);
            }
        }
        Ok(None)
    }
    pub(in crate::observed) fn outside(
        &self,
        target: &Self,
        env: &Environment<'_>,
    ) -> Result<Option<Vec<Scalar>>, ValidationFailure> {
        if self.particular.is_none() {
            return Ok(None);
        }
        if target.particular.is_none() {
            return Ok(self.particular.clone());
        }
        for (row, rhs) in target.equations.iter().zip(&target.rhs) {
            if let Some(point) = self.violation(row, rhs, env)? {
                return Ok(Some(point));
            }
        }
        Ok(None)
    }
}

pub(in crate::observed) fn change_guard_domain(
    env: &Environment<'_>,
    change: &Declaration,
    subject: &Scalar,
    missing: &mut Pending,
    ty: &Type,
) -> Result<NumericGuard, ValidationFailure> {
    let Signature::Change { params, guard, .. } = &change.signature else {
        return Err(internal!("数値guardの元宣言がchangeでない").into());
    };
    let first = params.first().ok_or(internal!("changeの第1引数がない"))?;
    let (vars, axes) =
        numeric_parameters::law_variables(env, params, &[(first.name.clone(), subject.clone())])?;
    numeric_guard_domain(env, *guard, &vars, &axes, &change.reading, missing, ty)
}
