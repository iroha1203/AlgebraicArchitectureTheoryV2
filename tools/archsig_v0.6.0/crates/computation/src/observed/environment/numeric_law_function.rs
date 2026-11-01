//! 数値Lawの全引数での零性を、既存の整数/体fiberで比較する。
use super::numeric_object_function::{self as source, Counterexample, Source};
use super::*;
use crate::{
    construction::{ConstructionFailure, readings::ObjectReadingInstances},
    observed::{
        affine::{self, TermArgument},
        field_fiber, integer_fiber, numeric,
        object_evaluation_table::ObjectEvaluationPosition,
        term::{affine as terms, affine::Value},
    },
};
use num_bigint::BigInt;
use num_traits::One;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Pending {
    pub location: archsig_common::issue::Location,
    pub missing: Vec<Fact>,
    pub unsupported_numeric: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Reading {
    // None は未決、空の等式列は全域で真。
    condition: Option<Vec<affine::Form>>,
    body: Option<affine::Form>,
    restriction: Option<GuardRestriction>,
    residual: Option<affine::Form>,
    facts: Vec<Fact>,
    pending: Option<Pending>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct GuardRestriction {
    body: affine::Form,
    basis: Vec<TermArgument>,
    guard: System,
    zero: System,
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Certificate {
    Integer(integer_fiber::Fiber),
    Field(field_fiber::Fiber),
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct System {
    coefficients: Vec<Vec<Scalar>>,
    rhs: Vec<Scalar>,
    certificate: Certificate,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Family {
    source: Reading,
    target: Reading,
    basis: Vec<TermArgument>,
    systems: Option<(System, System)>,
    condition_systems: Option<(System, System)>,
    pub applicable: Option<bool>,
    pub equivalent: Option<bool>,
    pub value_equal: Option<bool>,
    pub implies: Option<bool>,
    pub example: Option<Counterexample>,
    pub application_example: Option<Counterexample>,
    pub value_example: Option<Counterexample>,
    pub pending: Option<Pending>,
}
#[track_caller]
fn bad(s: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(internal!(s))
}
fn invalid(e: ValidationFailure) -> ConstructionFailure {
    match e {
        ValidationFailure::Stop(s) => s.into(),
        e => bad(&format!("数値Lawの全引数比較: {e:?}")),
    }
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectLawFamily)
        .map_err(Into::into)
}
fn pending(span: (usize, usize), missing: Vec<Fact>) -> Pending {
    Pending {
        location: archsig_common::issue::Location::Law { span },
        missing,
        unsupported_numeric: false,
    }
}
fn read(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    position: ObjectEvaluationPosition,
    names: &[(String, String)],
    target: bool,
    assignments: &[(String, Scalar)],
    c: &Control,
) -> Result<Reading, ConstructionFailure> {
    let row = &readings.instances()[position.instance];
    let declaration = &inputs.law().declarations()[&row.declaration().name];
    let archsig_input::law::model::Signature::Law { body, guard, .. } = &declaration.signature
    else {
        return Err(bad("数値Lawを選択する"));
    };
    let zero_type =
        match crate::observed::object_law_residuals::predicate_equation(inputs, *body, c)? {
            Some(id) => match inputs.law().exprs()[id].kind {
                archsig_input::law::ast::ExprKind::Binary { lhs, .. } => inputs
                    .law()
                    .expr_type(lhs)
                    .cloned()
                    .filter(|t| matches!(t, Type::Z | Type::Q))
                    .unwrap_or(Type::Z),
                _ => Type::Z,
            },
            None => Type::Z,
        };
    let outside = |c: &Control, facts: Vec<Fact>| -> Result<Reading, ConstructionFailure> {
        let zero = numeric::zero(&zero_type, c).map_err(invalid)?;
        Ok(Reading {
            body: None,
            restriction: None,
            condition: Some(vec![
                affine::constant(&Scalar::Z(1.into()), c)
                    .map_err(invalid)?
                    .ok_or_else(|| bad("偽の適用式がない"))?,
            ]),
            residual: affine::constant(&zero, c).map_err(invalid)?,
            facts,
            pending: None,
        })
    };
    let mut condition = vec![];
    let mut facts = vec![];
    let unknown = |span, missing, facts, condition| Reading {
        body: None,
        restriction: None,
        condition,
        residual: None,
        facts,
        pending: Some(pending(span, missing)),
    };
    if let Some(guard) = guard {
        let (source, analysis) = source::guard(
            inputs,
            readings,
            (position, Some(*guard)),
            names,
            target,
            assignments,
            c,
        )?;
        let value = match source {
            Source::Outside => return outside(c, facts),
            Source::Unknown => {
                return Ok(unknown(
                    inputs.law().exprs()[*guard].span,
                    vec![],
                    facts,
                    None,
                ));
            }
            Source::Value(value) => value,
        };
        facts.extend(value.support.iter().cloned());
        if value.condition_failed || value.condition_pending {
            return Ok(unknown(
                inputs.law().exprs()[*guard].span,
                analysis.missing,
                facts,
                None,
            ));
        }
        match value.known_value {
            Some(Scalar::Bool(false)) => return outside(c, facts),
            Some(Scalar::Bool(true)) => {}
            _ => {
                let Some(forms) = analysis.forms else {
                    let mut reading = unknown(
                        inputs.law().exprs()[*guard].span,
                        analysis.missing,
                        facts,
                        None,
                    );
                    if let Some(pending) = &mut reading.pending {
                        pending.unsupported_numeric = analysis.unsupported_numeric;
                    }
                    return Ok(reading);
                };
                let mut missing = forms
                    .iter()
                    .flat_map(|f| f.missing_facts())
                    .collect::<Vec<_>>();
                missing.sort();
                missing.dedup();
                for form in &forms {
                    if form.numeric_parameter_terms(c).map_err(invalid)?.is_none() {
                        return Ok(unknown(
                            inputs.law().exprs()[*guard].span,
                            missing,
                            facts,
                            None,
                        ));
                    }
                }
                condition = forms;
            }
        }
    }
    let value = match source::expression(
        inputs,
        readings,
        (position, None),
        names,
        target,
        assignments,
        c,
    )? {
        Source::Outside => return outside(c, facts),
        Source::Unknown => {
            return Ok(unknown(
                inputs.law().exprs()[*body].span,
                vec![],
                facts,
                None,
            ));
        }
        Source::Value(value) => *value,
    };
    facts.extend(value.support);
    facts.sort();
    facts.dedup();
    let incomplete = |missing| {
        unknown(
            inputs.law().exprs()[*body].span,
            missing,
            facts.clone(),
            Some(condition.clone()),
        )
    };
    if value.condition_failed || value.condition_pending {
        return Ok(incomplete(vec![]));
    }
    let Some(comparison) = value.comparison else {
        return Ok(incomplete(vec![]));
    };
    if comparison.op != BinOp::Eq || !comparison.bound_axes.is_empty() {
        return Ok(incomplete(vec![]));
    }
    let Some(residual) = affine::binary(
        BinOp::Sub,
        Some(&comparison.left),
        Some(&comparison.right),
        c,
    )
    .map_err(invalid)?
    else {
        return Ok(incomplete(vec![]));
    };
    if residual
        .numeric_parameter_terms(c)
        .map_err(invalid)?
        .is_none()
    {
        return Ok(incomplete(residual.missing_facts()));
    }
    let restriction = if condition_value(&condition, c).map_err(invalid)?.is_none() {
        restrict_zeros(&condition, &residual, c).map_err(invalid)?
    } else {
        None
    };
    let body = Some(residual.clone());
    let residual = if restriction.is_some() {
        let zero = numeric::zero(&zero_type, c).map_err(invalid)?;
        Some(
            affine::constant(&zero, c)
                .map_err(invalid)?
                .ok_or_else(|| bad("条件付き残差の零がない"))?,
        )
    } else if condition_value(&condition, c).map_err(invalid)?.is_none() {
        // 非定数guardのindicatorを線形式へ置き換えない。
        None
    } else {
        Some(residual)
    };
    Ok(Reading {
        condition: Some(condition),
        body,
        restriction,
        residual,
        facts,
        pending: None,
    })
}

fn rational(value: &Scalar) -> Result<Scalar, ValidationFailure> {
    match value {
        Scalar::Z(n) => Ok(Scalar::Q(n.clone(), 1.into())),
        Scalar::Q(..) => Ok(value.clone()),
        _ => Err(internal!("数値Lawの係数がZ/Qでない").into()),
    }
}
fn integer_row(values: &[Scalar], c: &Control) -> Result<Vec<BigInt>, ValidationFailure> {
    let mut denominator = BigInt::one();
    for v in values {
        tick(c)?;
        if let Scalar::Q(_, d) = v {
            denominator *= d;
        } else if !matches!(v, Scalar::Z(_)) {
            return Err(internal!("整数Law係数がZ/Qでない").into());
        }
    }
    values
        .iter()
        .map(|v| {
            tick(c)?;
            match v {
                Scalar::Z(n) => Ok(n * &denominator),
                Scalar::Q(n, d) => Ok(n * (&denominator / d)),
                _ => Err(internal!("整数Law係数がZ/Qでない").into()),
            }
        })
        .collect()
}
fn system(
    form: &affine::Form,
    basis: &[TermArgument],
    ground: &Type,
    c: &Control,
) -> Result<System, ValidationFailure> {
    systems(std::slice::from_ref(form), basis, ground, c)
}
fn systems(
    forms: &[affine::Form],
    basis: &[TermArgument],
    ground: &Type,
    c: &Control,
) -> Result<System, ValidationFailure> {
    let mut coefficients = vec![];
    let mut rhs = vec![];
    for form in forms {
        let (constant, terms) = form
            .numeric_parameter_terms(c)?
            .ok_or(internal!("数値Lawに未確定の係数がある"))?;
        let zero = numeric::zero(&constant.ty(), c)?;
        let mut row = vec![];
        for key in basis {
            tick(c)?;
            row.push(
                terms
                    .iter()
                    .find(|(k, _)| k == key)
                    .map(|(_, v)| v.clone())
                    .unwrap_or_else(|| zero.clone()),
            );
        }
        let right = numeric::binary(BinOp::Sub, &zero, &constant, c)?;
        coefficients.push(row);
        rhs.push(right);
    }
    if coefficients.is_empty() {
        // Systemの行からも列数を読めるよう、全域を零の一行で表す。
        coefficients.push(vec![numeric::zero(ground, c)?; basis.len()]);
        rhs.push(numeric::zero(ground, c)?);
    }
    solve_system(coefficients, rhs, basis.len(), ground, c)
}
fn solve_system(
    rows: Vec<Vec<Scalar>>,
    rhs: Vec<Scalar>,
    cols: usize,
    ground: &Type,
    c: &Control,
) -> Result<System, ValidationFailure> {
    if *ground == Type::Z {
        let mut matrix = vec![];
        let mut right = vec![];
        for (mut row, value) in rows.into_iter().zip(rhs) {
            tick(c)?;
            row.push(value);
            let mut row = integer_row(&row, c)?;
            right.push(row.pop().ok_or(internal!("整数fiberの右辺がない"))?);
            matrix.push(row);
        }
        let certificate = integer_fiber::solve(&matrix, cols, &right, c)?;
        Ok(System {
            coefficients: matrix
                .into_iter()
                .map(|row| row.into_iter().map(Scalar::Z).collect())
                .collect(),
            rhs: right.into_iter().map(Scalar::Z).collect(),
            certificate: Certificate::Integer(certificate),
        })
    } else {
        let rows = rows
            .iter()
            .map(|row| row.iter().map(rational).collect::<Result<Vec<_>, _>>())
            .collect::<Result<Vec<_>, _>>()?;
        let rhs = rhs.iter().map(rational).collect::<Result<Vec<_>, _>>()?;
        let certificate = field_fiber::solve(&Type::Q, &rows, cols, &rhs, c)?;
        Ok(System {
            coefficients: rows,
            rhs,
            certificate: Certificate::Field(certificate),
        })
    }
}
fn condition_value(forms: &[affine::Form], c: &Control) -> Result<Option<bool>, ValidationFailure> {
    let mut known = true;
    for form in forms {
        match form.value(c)? {
            Some(value) if value != numeric::zero(&value.ty(), c)? => return Ok(Some(false)),
            Some(_) => {}
            None => known = false,
        }
    }
    Ok(known.then_some(true))
}

impl System {
    fn point(&self) -> Option<Vec<Scalar>> {
        match &self.certificate {
            Certificate::Integer(f) => f
                .particular
                .as_ref()
                .map(|p| p.iter().cloned().map(Scalar::Z).collect()),
            Certificate::Field(f) => f.particular.clone(),
        }
    }
    fn directions(&self) -> Vec<Vec<Scalar>> {
        match &self.certificate {
            Certificate::Integer(f) => f
                .kernel
                .iter()
                .map(|r| r.iter().cloned().map(Scalar::Z).collect())
                .collect(),
            Certificate::Field(f) => f.kernel.clone(),
        }
    }
    fn contains(&self, point: &[Scalar], c: &Control) -> Result<bool, ValidationFailure> {
        for (row, rhs) in self.coefficients.iter().zip(&self.rhs) {
            tick(c)?;
            if row.len() != point.len() {
                return Err(internal!("数値Law反例の次元が違う").into());
            }
            let mut value = numeric::zero(&rhs.ty(), c)?;
            for (a, x) in row.iter().zip(point) {
                tick(c)?;
                value = numeric::binary(
                    BinOp::Add,
                    &value,
                    &numeric::binary(BinOp::Mul, a, x, c)?,
                    c,
                )?;
            }
            if value != *rhs {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
// affine fiberの全点はparticularとkernel基底で生成される。
// 他方の線形式がparticularと各particular+基底で零なら、全fiberでも零。
// 両方向を検査し、異なる場合だけその実点を元Lawへ再代入する。
fn outside(a: &System, b: &System, c: &Control) -> Result<Option<Vec<Scalar>>, ValidationFailure> {
    let Some(point) = a.point() else {
        return Ok(None);
    };
    if !b.contains(&point, c)? {
        return Ok(Some(point));
    }
    let directions = a.directions();
    for column in 0..directions.first().map_or(0, Vec::len) {
        tick(c)?;
        let moved = point
            .iter()
            .zip(&directions)
            .map(|(x, row)| numeric::binary(BinOp::Add, x, &row[column], c))
            .collect::<Result<Vec<_>, _>>()?;
        if !b.contains(&moved, c)? {
            return Ok(Some(moved));
        }
    }
    Ok(None)
}
fn guard_fiber(
    guard: &[affine::Form],
    body: &affine::Form,
    c: &Control,
) -> Result<Option<GuardRestriction>, ValidationFailure> {
    let mut basis = BTreeSet::new();
    let mut rational = false;
    for form in guard.iter().chain(std::iter::once(body)) {
        let Some((constant, terms)) = form.numeric_parameter_terms(c)? else {
            return Ok(None);
        };
        rational |= constant.ty() == Type::Q;
        basis.extend(terms.into_iter().map(|(axis, _)| axis));
    }
    let basis: Vec<_> = basis.into_iter().collect();
    let ground = basis
        .first()
        .map(|axis| axis.kind.ty())
        .unwrap_or(if rational { Type::Q } else { Type::Z });
    if basis.iter().any(|axis| axis.kind.ty() != ground) {
        return Ok(None);
    }
    let guard_system = systems(guard, &basis, &ground, c)?;
    let body_system = system(body, &basis, &ground, c)?;
    Ok(Some(GuardRestriction {
        body: body.clone(),
        basis,
        guard: guard_system,
        zero: body_system,
    }))
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum GuardTruth {
    Holds,
    /// guardまたは本文に現れる軸の部分割当て。元の全binder列へ上書きして使う。
    Refuted(Vec<(affine::Parameter, Scalar)>),
}
impl GuardRestriction {
    pub(in crate::observed) fn is_zero(&self, c: &Control) -> Result<bool, ValidationFailure> {
        Ok(outside(&self.guard, &self.zero, c)?.is_none())
    }
}
#[cfg(test)]
fn restrict_zero(
    guard: &affine::Form,
    body: &affine::Form,
    c: &Control,
) -> Result<Option<GuardRestriction>, ValidationFailure> {
    restrict_zeros(std::slice::from_ref(guard), body, c)
}
fn restrict_zeros(
    guard: &[affine::Form],
    body: &affine::Form,
    c: &Control,
) -> Result<Option<GuardRestriction>, ValidationFailure> {
    let Some(proof) = guard_fiber(guard, body, c)? else {
        return Ok(None);
    };
    Ok(if proof.is_zero(c)? { Some(proof) } else { None })
}
/// 全称binderの出現を同じ位置軸へ移し、適用fiber内の実反例を求める。
pub(in crate::observed) fn universal_on_guards(
    guard: &[affine::Form],
    body: &affine::Form,
    c: &Control,
) -> Result<Option<GuardTruth>, ValidationFailure> {
    let Some((ba, bt)) = body.parameter_coordinates(c)? else {
        return Ok(None);
    };
    let mut rows = vec![];
    for form in guard {
        let Some(row) = form.parameter_coordinates(c)? else {
            return Ok(None);
        };
        rows.push(row);
    }
    let parameters = rows
        .iter()
        .flat_map(|(_, terms)| terms)
        .chain(&bt)
        .map(|(p, _)| p.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let convert = |constant: &Scalar,
                   terms: &[(affine::Parameter, Scalar)]|
     -> Result<affine::Form, ValidationFailure> {
        let mut form =
            affine::constant(constant, c)?.ok_or(internal!("fiberの定数型が数値でない"))?;
        for (parameter, coefficient) in terms {
            tick(c)?;
            let position = parameters
                .iter()
                .position(|p| p == parameter)
                .ok_or(internal!("fiberの元binderがない"))?;
            let axis = affine::term_argument(
                TermArgument {
                    argument: position,
                    component: vec![],
                    kind: parameter.kind,
                },
                c,
            )?;
            let coefficient =
                affine::constant(coefficient, c)?.ok_or(internal!("fiberの係数が数値でない"))?;
            let term = affine::binary(BinOp::Mul, Some(&axis), Some(&coefficient), c)?
                .ok_or(internal!("fiberの項がアフィンでない"))?;
            form = affine::binary(BinOp::Add, Some(&form), Some(&term), c)?
                .ok_or(internal!("fiberの和がアフィンでない"))?;
        }
        Ok(form)
    };
    let ground = parameters.first().map(|p| p.kind.ty()).unwrap_or_else(|| {
        if rows.iter().any(|(constant, _)| constant.ty() == Type::Q) || ba.ty() == Type::Q {
            Type::Q
        } else {
            Type::Z
        }
    });
    if parameters.iter().any(|p| p.kind.ty() != ground) {
        return Ok(None);
    }
    let basis = parameters
        .iter()
        .enumerate()
        .map(|(argument, parameter)| TermArgument {
            argument,
            component: vec![],
            kind: parameter.kind,
        })
        .collect::<Vec<_>>();
    let guards = rows
        .iter()
        .map(|(constant, terms)| convert(constant, terms))
        .collect::<Result<Vec<_>, _>>()?;
    let guard = systems(&guards, &basis, &ground, c)?;
    let body = system(&convert(&ba, &bt)?, &basis, &ground, c)?;
    Ok(Some(match outside(&guard, &body, c)? {
        None => GuardTruth::Holds,
        Some(point) => GuardTruth::Refuted(parameters.into_iter().zip(point).collect()),
    }))
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum GuardValue {
    Outside,
    Known {
        proof: Box<GuardRestriction>,
        support: Vec<Fact>,
    },
    Pending {
        pending: Pending,
        support: Vec<Fact>,
    },
}
/// 元のguardと本文を通常Evaluatorで読み、全適用fiberの正確な表示を保持する。
/// 原式・特解・整数/体kernelを保持し、元の差を零へ書き換えない。
pub(in crate::observed) fn on_guard(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    position: ObjectEvaluationPosition,
    finite: &[(String, Scalar)],
    c: &Control,
) -> Result<Option<GuardValue>, ConstructionFailure> {
    let row = &readings.instances()[position.instance];
    let names = row
        .declaration()
        .parameters
        .iter()
        .map(|(n, _)| (n.clone(), n.clone()))
        .collect::<Vec<_>>();
    let reading = read(inputs, readings, position, &names, false, finite, c)?;
    if let Some(pending) = reading.pending {
        return Ok(
            if pending.missing.is_empty() && !pending.unsupported_numeric {
                None
            } else {
                Some(GuardValue::Pending {
                    pending,
                    support: reading.facts,
                })
            },
        );
    }
    let (Some(guard), Some(body)) = (reading.condition, reading.body.or(reading.residual)) else {
        return Ok(None);
    };
    let Some(proof) = guard_fiber(&guard, &body, c).map_err(invalid)? else {
        return Ok(None);
    };
    Ok(Some(GuardValue::Known {
        proof: Box::new(proof),
        support: reading.facts,
    }))
}
// 有限個の等式を同じ正確なfiberへまとめる。guardの共通域に使う。
fn intersection(a: &System, b: &System, c: &Control) -> Result<System, ValidationFailure> {
    let cols = a
        .coefficients
        .first()
        .ok_or(internal!("fiberの行がない"))?
        .len();
    let mut rows = vec![];
    let mut rhs = vec![];
    for (row, value) in a
        .coefficients
        .iter()
        .zip(&a.rhs)
        .chain(b.coefficients.iter().zip(&b.rhs))
    {
        tick(c)?;
        if row.len() != cols {
            return Err(internal!("fiberの共通域の列数が違う").into());
        }
        rows.push(row.clone());
        rhs.push(value.clone());
    }
    let ground = match (&a.certificate, &b.certificate) {
        (Certificate::Integer(_), Certificate::Integer(_)) => Type::Z,
        (Certificate::Field(_), Certificate::Field(_)) => Type::Q,
        _ => return Err(internal!("fiberの共通域の係数型が違う").into()),
    };
    solve_system(rows, rhs, cols, &ground, c)
}
// 二つの真のアフィン部分空間は、Z/Qの非空fiber全体を覆わない。
// p∉a,p∈b,q∈a,q∉bなら、2p-qは同じfiber内で両方の外にある。
fn outside_both(
    base: &System,
    a: &System,
    b: &System,
    c: &Control,
) -> Result<Option<Vec<Scalar>>, ValidationFailure> {
    let Some(p) = outside(base, a, c)? else {
        return Ok(None);
    };
    if !b.contains(&p, c)? {
        return Ok(Some(p));
    }
    let Some(q) = outside(base, b, c)? else {
        return Ok(None);
    };
    if !a.contains(&q, c)? {
        return Ok(Some(q));
    }
    let point = p
        .iter()
        .zip(q)
        .map(|(p, q)| {
            tick(c)?;
            numeric::binary(BinOp::Add, p, &numeric::binary(BinOp::Sub, p, &q, c)?, c)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if !base.contains(&point, c)? || a.contains(&point, c)? || b.contains(&point, c)? {
        return Err(internal!("二つの零fiberを分離する元点の再検査に失敗した").into());
    }
    Ok(Some(point))
}
// 条件付き残差が非零の族はG\D。包含の反例は
// (Ga∩Dz)\Da と Ga\(Da∪Gz) の二つに分け、元の全域で検査する。
fn conditional_outside(
    ga: &System,
    da: &System,
    gz: &System,
    dz: &System,
    c: &Control,
) -> Result<Option<Vec<Scalar>>, ValidationFailure> {
    let common = intersection(ga, dz, c)?;
    let point = match outside(&common, da, c)? {
        Some(p) => Some(p),
        None => outside_both(ga, da, gz, c)?,
    };
    if let Some(p) = &point
        && (!ga.contains(p, c)?
            || da.contains(p, c)?
            || (gz.contains(p, c)? && !dz.contains(p, c)?))
    {
        return Err(internal!("条件付き残差の反例が元の適用域を分離しない").into());
    }
    Ok(point)
}
fn assignments(
    inputs: &CheckedInputs,
    row: &crate::construction::readings::ObjectInstance,
    names: &[(String, String)],
    basis: &[TermArgument],
    point: &[Scalar],
    bound: &[(String, Scalar)],
    c: &Control,
) -> Result<Vec<(String, Scalar)>, ValidationFailure> {
    let mut result = bound.to_vec();
    for p in row
        .parameters()
        .iter()
        .filter(|p| !bound.iter().any(|(name, _)| name == &p.name))
    {
        tick(c)?;
        let argument = names
            .iter()
            .position(|(a, _)| a == &p.name)
            .ok_or(internal!("数値Lawの引数対応がない"))?;
        let Some(domain) = terms::domain(&p.ty, argument, &[], inputs.law(), c)? else {
            return Err(internal!("数値Lawの引数型が数値でない").into());
        };
        let [domain] = domain.as_slice() else {
            return Err(internal!("数値Lawの記号域が一つでない").into());
        };
        let mut pending = vec![domain];
        let mut keys = vec![];
        while let Some(value) = pending.pop() {
            tick(c)?;
            match value {
                Value::Number(f) => {
                    let (_, terms) = f
                        .numeric_parameter_terms(c)?
                        .ok_or(internal!("数値Lawの引数軸がない"))?;
                    keys.extend(terms.into_iter().map(|(k, _)| k));
                }
                Value::Tuple(v) => pending.extend(v.iter().rev()),
                _ => return Err(internal!("数値Lawの引数形が違う").into()),
            }
        }
        let mut values = keys
            .iter()
            .map(|key| {
                basis
                    .iter()
                    .position(|k| k == key)
                    .map(|i| Ok(point[i].clone()))
                    .unwrap_or_else(|| numeric::zero(&key.kind.ty(), c))
            })
            .collect::<Result<Vec<_>, ValidationFailure>>()?
            .into_iter();
        let value = numeric_parameters::restore(
            &p.ty,
            c,
            &mut || {
                values
                    .next()
                    .ok_or_else(|| internal!("数値Lawの反例成分が足りない").into())
            },
            &Scalar::Tuple,
        )?;
        result.push((p.name.clone(), value));
    }
    Ok(result)
}
#[derive(Clone, Copy)]
enum ComparisonKind {
    Application,
    Zero,
    Value,
}
pub(in crate::observed) fn compare(
    inputs: &CheckedInputs,
    readings: [&ObjectReadingInstances; 2],
    positions: [ObjectEvaluationPosition; 2],
    names: &[(String, String)],
    c: &Control,
) -> Result<Family, ConstructionFailure> {
    compare_bound(inputs, readings, positions, names, [&[], &[]], c)
}
pub(in crate::observed) fn compare_bound(
    inputs: &CheckedInputs,
    readings: [&ObjectReadingInstances; 2],
    positions: [ObjectEvaluationPosition; 2],
    names: &[(String, String)],
    bound: [&[(String, Scalar)]; 2],
    c: &Control,
) -> Result<Family, ConstructionFailure> {
    let a = read(inputs, readings[0], positions[0], names, false, bound[0], c)?;
    let z = read(inputs, readings[1], positions[1], names, true, bound[1], c)?;
    let mut result = Family {
        applicable: None,
        equivalent: None,
        value_equal: None,
        implies: None,
        example: None,
        application_example: None,
        value_example: None,
        pending: a.pending.clone().or_else(|| z.pending.clone()),
        source: a,
        target: z,
        basis: vec![],
        systems: None,
        condition_systems: None,
    };
    let forms = [
        result
            .source
            .body
            .as_ref()
            .or(result.source.residual.as_ref()),
        result
            .target
            .body
            .as_ref()
            .or(result.target.residual.as_ref()),
    ];
    let mut rational_ground = false;
    let mut keys = BTreeSet::new();
    for form in result
        .source
        .condition
        .iter()
        .flatten()
        .chain(result.target.condition.iter().flatten())
        .chain(forms.into_iter().flatten())
    {
        let (constant, terms) = form
            .numeric_parameter_terms(c)
            .map_err(invalid)?
            .ok_or_else(|| bad("数値Lawの係数がない"))?;
        rational_ground |= constant.ty() == Type::Q;
        keys.extend(terms.into_iter().map(|(k, _)| k));
    }
    result.basis = keys.into_iter().collect();
    let ground = result
        .basis
        .first()
        .map(|k| k.kind.ty())
        .unwrap_or(if rational_ground { Type::Q } else { Type::Z });
    if result.basis.iter().any(|k| k.kind.ty() != ground) {
        result.pending = Some(pending(
            inputs.law().declarations()[&readings[0].instances()[positions[0].instance]
                .declaration()
                .name]
                .span,
            vec![],
        ));
        return Ok(result);
    }
    let mut points = vec![];
    if let (Some(a), Some(z)) = (&result.source.condition, &result.target.condition) {
        if let (Some(a), Some(z)) = (
            condition_value(a, c).map_err(invalid)?,
            condition_value(z, c).map_err(invalid)?,
        ) {
            let equal = a == z;
            result.applicable = Some(equal);
            if !equal {
                points.push((
                    ComparisonKind::Application,
                    result
                        .basis
                        .iter()
                        .map(|axis| numeric::zero(&axis.kind.ty(), c))
                        .collect::<Result<Vec<_>, _>>()
                        .map_err(invalid)?,
                ));
            }
        } else {
            let sa = systems(a, &result.basis, &ground, c).map_err(invalid)?;
            let sz = systems(z, &result.basis, &ground, c).map_err(invalid)?;
            let point = match outside(&sa, &sz, c).map_err(invalid)? {
                Some(p) => Some(p),
                None => outside(&sz, &sa, c).map_err(invalid)?,
            };
            result.applicable = Some(point.is_none());
            if let Some(point) = point {
                points.push((ComparisonKind::Application, point));
            }
            result.condition_systems = Some((sa, sz));
        }
    }
    let body_forms = if result.condition_systems.is_some() {
        (
            result
                .source
                .body
                .as_ref()
                .or(result.source.residual.as_ref()),
            result
                .target
                .body
                .as_ref()
                .or(result.target.residual.as_ref()),
        )
    } else {
        (
            result.source.residual.as_ref(),
            result.target.residual.as_ref(),
        )
    };
    if let (Some(a), Some(z)) = body_forms {
        let sa = system(a, &result.basis, &ground, c).map_err(invalid)?;
        let sz = system(z, &result.basis, &ground, c).map_err(invalid)?;
        let implication_counterexample = match &result.condition_systems {
            Some((ga, gz)) => conditional_outside(ga, &sa, gz, &sz, c),
            None => outside(&sz, &sa, c),
        }
        .map_err(invalid)?;
        result.implies = Some(implication_counterexample.is_none());
        let point = match implication_counterexample {
            Some(p) => Some(p),
            None => match &result.condition_systems {
                Some((ga, gz)) => conditional_outside(gz, &sz, ga, &sa, c),
                None => outside(&sa, &sz, c),
            }
            .map_err(invalid)?,
        };
        result.equivalent = Some(point.is_none());
        if let Some(point) = point {
            points.push((ComparisonKind::Zero, point));
        }
        if a.ty(c).map_err(invalid)? == z.ty(c).map_err(invalid)? {
            let difference = affine::binary(BinOp::Sub, Some(a), Some(z), c)
                .map_err(invalid)?
                .ok_or_else(|| bad("数値残差族の差がアフィンでない"))?;
            let zero_difference =
                system(&difference, &result.basis, &ground, c).map_err(invalid)?;
            let value_point = if let Some((ga, gz)) = &result.condition_systems {
                let common = intersection(ga, gz, c).map_err(invalid)?;
                match outside(&common, &zero_difference, c).map_err(invalid)? {
                    Some(point) => Some(point),
                    None => match outside_both(ga, &sa, gz, c).map_err(invalid)? {
                        Some(point) => Some(point),
                        None => outside_both(gz, &sz, ga, c).map_err(invalid)?,
                    },
                }
            } else {
                let zero = numeric::zero(&ground, c).map_err(invalid)?;
                let zero = affine::constant(&zero, c)
                    .map_err(invalid)?
                    .ok_or_else(|| bad("数値全域の零がない"))?;
                outside(
                    &system(&zero, &result.basis, &ground, c).map_err(invalid)?,
                    &zero_difference,
                    c,
                )
                .map_err(invalid)?
            };
            result.value_equal = Some(value_point.is_none());
            if let Some(point) = value_point {
                points.push((ComparisonKind::Value, point));
            }
        }
        result.systems = Some((sa, sz));
    }
    for (kind, point) in points {
        let row = &readings[0].instances()[positions[0].instance];
        let bindings =
            assignments(inputs, row, names, &result.basis, &point, bound[0], c).map_err(invalid)?;
        let mut target_bindings = bindings
            .iter()
            .filter(|(name, _)| !bound[0].iter().any(|(fixed, _)| fixed == name))
            .map(|(name, v)| {
                names
                    .iter()
                    .find(|(a, _)| a == name)
                    .map(|(_, z)| (z.clone(), v.clone()))
                    .ok_or_else(|| bad("数値Law反例の先引数がない"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        target_bindings.extend_from_slice(bound[1]);
        let a = read(
            inputs,
            readings[0],
            positions[0],
            names,
            false,
            &bindings,
            c,
        )?;
        let z = read(
            inputs,
            readings[1],
            positions[1],
            names,
            true,
            &target_bindings,
            c,
        )?;
        let (left, right) = if matches!(kind, ComparisonKind::Application) {
            let truth = |reading: &Reading| -> Result<Scalar, ConstructionFailure> {
                let forms = reading
                    .condition
                    .as_ref()
                    .ok_or_else(|| bad("Law反例の適用が未決"))?;
                Ok(Scalar::Bool(
                    condition_value(forms, c)
                        .map_err(invalid)?
                        .ok_or_else(|| bad("Law反例の適用が未決"))?,
                ))
            };
            (truth(&a)?, truth(&z)?)
        } else {
            let left = a
                .residual
                .as_ref()
                .map(|f| f.value(c))
                .transpose()
                .map_err(invalid)?
                .flatten()
                .ok_or_else(|| bad("元Law反例の再代入値がない"))?;
            let right = z
                .residual
                .as_ref()
                .map(|f| f.value(c))
                .transpose()
                .map_err(invalid)?
                .flatten()
                .ok_or_else(|| bad("先Law反例の再代入値がない"))?;
            if matches!(kind, ComparisonKind::Zero)
                && (left == numeric::zero(&left.ty(), c).map_err(invalid)?)
                    == (right == numeric::zero(&right.ty(), c).map_err(invalid)?)
            {
                return Err(bad("数値Lawのfiber反例が元式の零性を分離しない"));
            }
            (left, right)
        };
        if left == right {
            return Err(bad("数値Lawの反例が相違しない"));
        }
        let mut facts = a.facts;
        facts.extend(z.facts);
        facts.sort();
        facts.dedup();
        let mut values = source::fixed_bindings(row, c).map_err(invalid)?;
        values.extend(bindings);
        let bindings = row
            .declaration()
            .parameters
            .iter()
            .map(|(name, _)| {
                values
                    .iter()
                    .find(|(n, _)| n == name)
                    .cloned()
                    .ok_or_else(|| bad("数値Law反例の全引数がない"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let example = Counterexample {
            bindings,
            left,
            right,
            facts,
        };
        match kind {
            ComparisonKind::Application => result.application_example = Some(example),
            ComparisonKind::Zero => result.example = Some(example),
            ComparisonKind::Value => result.value_example = Some(example),
        }
    }
    Ok(result)
}

#[cfg(test)]
mod guard_tests {
    use super::*;
    #[test]
    fn conjunctive_guard_fibers_use_all_rows_and_preserve_integer_solvability() {
        for kind in [affine::NumberType::Z, affine::NumberType::Q] {
            let c = Control::unlimited();
            let axis = |argument| {
                affine::term_argument(
                    TermArgument {
                        argument,
                        component: vec![],
                        kind,
                    },
                    &c,
                )
                .unwrap()
            };
            let x = axis(0);
            let y = axis(1);
            let number = |n: i64| {
                affine::constant(
                    &if kind == affine::NumberType::Z {
                        Scalar::Z(n.into())
                    } else {
                        Scalar::Q(n.into(), 1.into())
                    },
                    &c,
                )
                .unwrap()
                .unwrap()
            };
            let op = |op, a: &affine::Form, b: &affine::Form| {
                affine::binary(op, Some(a), Some(b), &c).unwrap().unwrap()
            };
            let one = number(1);
            let x_minus_one = op(BinOp::Sub, &x, &one);
            assert!(
                restrict_zeros(&[x.clone(), x_minus_one], &one, &c)
                    .unwrap()
                    .is_some()
            );
            let y_minus_one = op(BinOp::Sub, &y, &one);
            let proof = guard_fiber(&[x.clone(), y_minus_one], &op(BinOp::Sub, &x, &y), &c)
                .unwrap()
                .unwrap();
            assert!(!proof.is_zero(&c).unwrap());
            let point = outside(&proof.guard, &proof.zero, &c).unwrap().unwrap();
            assert_eq!(
                point,
                if kind == affine::NumberType::Z {
                    vec![Scalar::Z(0.into()), Scalar::Z(1.into())]
                } else {
                    vec![Scalar::Q(0.into(), 1.into()), Scalar::Q(1.into(), 1.into())]
                }
            );
            let half = op(BinOp::Sub, &op(BinOp::Mul, &number(2), &x), &one);
            assert_eq!(
                restrict_zeros(&[half, y], &one, &c).unwrap().is_some(),
                kind == affine::NumberType::Z
            );
        }
    }
    #[test]
    fn guard_fiber_zero_requires_every_kernel_direction_and_exact_ground() {
        for kind in [affine::NumberType::Z, affine::NumberType::Q] {
            let c = Control::unlimited();
            let x = affine::term_argument(
                TermArgument {
                    argument: 0,
                    component: vec![],
                    kind,
                },
                &c,
            )
            .unwrap();
            let y = affine::term_argument(
                TermArgument {
                    argument: 1,
                    component: vec![],
                    kind,
                },
                &c,
            )
            .unwrap();
            let number = |n: i64| {
                if kind == affine::NumberType::Z {
                    Scalar::Z(n.into())
                } else {
                    Scalar::Q(n.into(), 1.into())
                }
            };
            let form = |n| affine::constant(&number(n), &c).unwrap().unwrap();
            let binary = |op, a: &affine::Form, b: &affine::Form| {
                affine::binary(op, Some(a), Some(b), &c).unwrap().unwrap()
            };
            assert!(restrict_zero(&x, &x, &c).unwrap().is_some());
            assert!(restrict_zero(&x, &y, &c).unwrap().is_none());
            assert!(
                restrict_zero(&x, &binary(BinOp::Sub, &x, &form(1)), &c)
                    .unwrap()
                    .is_none()
            );
            let twice_x = binary(BinOp::Mul, &form(2), &x);
            let guard = binary(BinOp::Sub, &twice_x, &form(1));
            let body = binary(BinOp::Sub, &binary(BinOp::Mul, &form(4), &x), &form(2));
            assert!(restrict_zero(&guard, &body, &c).unwrap().is_some());
            // 2x=1 has no integer point, but the rational fiber contains x=1/2.
            assert_eq!(
                restrict_zero(&guard, &form(1), &c).unwrap().is_some(),
                kind == affine::NumberType::Z
            );
        }
    }
    #[test]
    fn conditional_fiber_inclusion_checks_both_nonzero_branches() {
        for kind in [affine::NumberType::Z, affine::NumberType::Q] {
            let c = Control::unlimited();
            let keys = [
                TermArgument {
                    argument: 0,
                    component: vec![],
                    kind,
                },
                TermArgument {
                    argument: 1,
                    component: vec![],
                    kind,
                },
            ];
            let x = affine::term_argument(keys[0].clone(), &c).unwrap();
            let y = affine::term_argument(keys[1].clone(), &c).unwrap();
            let n = |v: i64| {
                if kind == affine::NumberType::Z {
                    Scalar::Z(v.into())
                } else {
                    Scalar::Q(v.into(), 1.into())
                }
            };
            let form = |v| affine::constant(&n(v), &c).unwrap().unwrap();
            let op = |op, a: &affine::Form, b: &affine::Form| {
                affine::binary(op, Some(a), Some(b), &c).unwrap().unwrap()
            };
            let ground = kind.ty();
            let sys = |f: &affine::Form| system(f, &keys, &ground, &c).unwrap();
            let all = sys(&form(0));
            let empty = sys(&form(1));
            let gx = sys(&x);
            let dy = sys(&y);
            let twice_y = sys(&op(BinOp::Mul, &form(2), &y));
            assert!(
                conditional_outside(&gx, &dy, &gx, &twice_y, &c)
                    .unwrap()
                    .is_none()
            );
            assert!(
                conditional_outside(&gx, &twice_y, &gx, &dy, &c)
                    .unwrap()
                    .is_none()
            );
            assert!(
                conditional_outside(&gx, &dy, &all, &dy, &c)
                    .unwrap()
                    .is_none()
            );
            let point = conditional_outside(&all, &dy, &gx, &dy, &c)
                .unwrap()
                .unwrap();
            assert_ne!(point[0], n(0));
            assert_ne!(point[1], n(0));
            assert!(
                conditional_outside(&gx, &gx, &empty, &empty, &c)
                    .unwrap()
                    .is_none()
            );
            let half = sys(&op(BinOp::Sub, &op(BinOp::Mul, &form(2), &x), &form(1)));
            let point = conditional_outside(&half, &empty, &empty, &empty, &c).unwrap();
            assert_eq!(point.is_some(), kind == affine::NumberType::Q);
            if let Some(point) = point {
                assert_eq!(point[0], Scalar::Q(1.into(), 2.into()));
            }
        }
    }
}
