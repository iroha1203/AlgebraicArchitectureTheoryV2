//! 数値Lawの全引数での零性を、既存の整数/体fiberで比較する。
use super::numeric_object_function::{self as source, Counterexample, Source};
use super::*;
use crate::{
    construction::{
        ConstructionFailure,
        readings::{ObjectEvaluationPosition, ObjectReadingInstances},
    },
    observed::{
        affine::{self, TermArgument},
        field_fiber, integer_fiber, numeric,
        term::affine::{self as terms, Value},
    },
};
use num_bigint::BigInt;
use num_traits::One;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Pending {
    pub location: crate::issue::Location,
    pub missing: Vec<Fact>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Reading {
    application: Option<bool>,
    residual: Option<affine::Form>,
    facts: Vec<Fact>,
    pending: Option<Pending>,
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
    pub applicable: Option<bool>,
    pub equivalent: Option<bool>,
    pub example: Option<Counterexample>,
    pub application_example: Option<Counterexample>,
    pub pending: Option<Pending>,
}
fn bad(s: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(s.into())
}
fn invalid(e: ValidationFailure) -> ConstructionFailure {
    match e {
        ValidationFailure::Stop(s) => s.into(),
        e => bad(&format!("数値Lawの全引数比較: {e:?}")),
    }
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.clone()
        .checkpoint(Checkpoint::ObjectLawFamily)
        .map_err(Into::into)
}
fn pending(span: (usize, usize), missing: Vec<Fact>) -> Pending {
    Pending {
        location: crate::issue::Location::Law { span },
        missing,
    }
}
fn read(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    position: ObjectEvaluationPosition,
    names: &[(String, String)],
    target: bool,
    assignments: &[(String, Scalar)],
    c: &mut Control,
) -> Result<Reading, ConstructionFailure> {
    let row = &readings.instances()[position.instance];
    let declaration = &inputs.law().declarations[&row.declaration().name];
    let crate::law::model::Signature::Law { body, guard, .. } = &declaration.signature else {
        return Err(bad("数値Lawを選択する"));
    };
    let outside = |c: &Control, facts: Vec<Fact>| -> Result<Reading, ConstructionFailure> {
        Ok(Reading {
            application: Some(false),
            residual: Some(
                affine::constant(&Scalar::Z(0.into()), c)
                    .map_err(invalid)?
                    .ok_or_else(|| bad("零の数値式がない"))?,
            ),
            facts,
            pending: None,
        })
    };
    let mut facts = vec![];
    if let Some(guard) = guard {
        match source::expression(
            inputs,
            readings,
            (position, Some(*guard)),
            names,
            target,
            assignments,
            c,
        )? {
            Source::Outside => return outside(c, facts),
            Source::Unknown => {
                return Ok(Reading {
                    application: None,
                    residual: None,
                    facts,
                    pending: Some(pending(inputs.law().exprs[*guard].span, vec![])),
                });
            }
            Source::Value(value) => {
                facts.extend(value.support.iter().cloned());
                if value.condition_failed || value.condition_pending {
                    return Ok(Reading {
                        application: None,
                        residual: None,
                        facts,
                        pending: Some(pending(inputs.law().exprs[*guard].span, vec![])),
                    });
                }
                match value.known_value {
                    Some(Scalar::Bool(false)) => return outside(c, facts),
                    Some(Scalar::Bool(true)) => {}
                    _ => {
                        return Ok(Reading {
                            application: None,
                            residual: None,
                            facts,
                            pending: Some(pending(inputs.law().exprs[*guard].span, vec![])),
                        });
                    }
                }
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
            return Ok(Reading {
                application: None,
                residual: None,
                facts,
                pending: Some(pending(inputs.law().exprs[*body].span, vec![])),
            });
        }
        Source::Value(value) => *value,
    };
    facts.extend(value.support);
    facts.sort();
    facts.dedup();
    let unknown = |missing| Reading {
        application: Some(true),
        residual: None,
        facts: facts.clone(),
        pending: Some(pending(inputs.law().exprs[*body].span, missing)),
    };
    if value.condition_failed || value.condition_pending {
        return Ok(unknown(vec![]));
    }
    let Some(comparison) = value.comparison else {
        return Ok(unknown(vec![]));
    };
    if comparison.op != BinOp::Eq || !comparison.bound_axes.is_empty() {
        return Ok(unknown(vec![]));
    }
    let Some(residual) = affine::binary(
        BinOp::Sub,
        Some(&comparison.left),
        Some(&comparison.right),
        c,
    )
    .map_err(invalid)?
    else {
        return Ok(unknown(vec![]));
    };
    if residual
        .numeric_parameter_terms(c)
        .map_err(invalid)?
        .is_none()
    {
        return Ok(unknown(residual.missing_facts()));
    }
    Ok(Reading {
        application: Some(true),
        residual: Some(residual),
        facts,
        pending: None,
    })
}
fn rational(value: &Scalar) -> Result<Scalar, ValidationFailure> {
    match value {
        Scalar::Z(n) => Ok(Scalar::Q(n.clone(), 1.into())),
        Scalar::Q(..) => Ok(value.clone()),
        _ => Err("数値Lawの係数がZ/Qでない".into()),
    }
}
fn integer_row(values: &[Scalar], c: &Control) -> Result<Vec<BigInt>, ValidationFailure> {
    let mut denominator = BigInt::one();
    for v in values {
        tick(c)?;
        if let Scalar::Q(_, d) = v {
            denominator *= d;
        } else if !matches!(v, Scalar::Z(_)) {
            return Err("整数Law係数がZ/Qでない".into());
        }
    }
    values
        .iter()
        .map(|v| {
            tick(c)?;
            match v {
                Scalar::Z(n) => Ok(n * &denominator),
                Scalar::Q(n, d) => Ok(n * (&denominator / d)),
                _ => Err("整数Law係数がZ/Qでない".into()),
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
    let (constant, terms) = form
        .numeric_parameter_terms(c)?
        .ok_or("数値Lawに未確定の係数がある")?;
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
    let rhs = numeric::binary(BinOp::Sub, &zero, &constant, c)?;
    if *ground == Type::Z {
        row.push(rhs);
        let mut coefficients = integer_row(&row, c)?;
        let rhs = coefficients.pop().ok_or("整数Lawの右辺がない")?;
        let certificate = integer_fiber::solve(
            &vec![coefficients.clone()],
            basis.len(),
            std::slice::from_ref(&rhs),
            c,
        )?;
        Ok(System {
            coefficients: vec![coefficients.into_iter().map(Scalar::Z).collect()],
            rhs: vec![Scalar::Z(rhs)],
            certificate: Certificate::Integer(certificate),
        })
    } else {
        let coefficients = vec![row.iter().map(rational).collect::<Result<Vec<_>, _>>()?];
        let rhs = vec![rational(&rhs)?];
        let certificate = field_fiber::solve(&Type::Q, &coefficients, basis.len(), &rhs, c)?;
        Ok(System {
            coefficients,
            rhs,
            certificate: Certificate::Field(certificate),
        })
    }
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
                return Err("数値Law反例の次元が違う".into());
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
fn assignments(
    inputs: &CheckedInputs,
    row: &crate::construction::readings::ObjectInstance,
    names: &[(String, String)],
    basis: &[TermArgument],
    point: &[Scalar],
    c: &Control,
) -> Result<Vec<(String, Scalar)>, ValidationFailure> {
    let mut result = vec![];
    for p in row.parameters() {
        tick(c)?;
        let argument = names
            .iter()
            .position(|(a, _)| a == &p.name)
            .ok_or("数値Lawの引数対応がない")?;
        let Some(domain) = terms::domain(&p.ty, argument, &[], inputs.law(), c)? else {
            return Err("数値Lawの引数型が数値でない".into());
        };
        let [domain] = domain.as_slice() else {
            return Err("数値Lawの記号域が一つでない".into());
        };
        let mut pending = vec![domain];
        let mut keys = vec![];
        while let Some(value) = pending.pop() {
            tick(c)?;
            match value {
                Value::Number(f) => {
                    let (_, terms) = f
                        .numeric_parameter_terms(c)?
                        .ok_or("数値Lawの引数軸がない")?;
                    keys.extend(terms.into_iter().map(|(k, _)| k));
                }
                Value::Tuple(v) => pending.extend(v.iter().rev()),
                _ => return Err("数値Lawの引数形が違う".into()),
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
                    .ok_or_else(|| "数値Lawの反例成分が足りない".into())
            },
            &Scalar::Tuple,
        )?;
        result.push((p.name.clone(), value));
    }
    Ok(result)
}
pub(in crate::observed) fn compare(
    inputs: &CheckedInputs,
    readings: [&ObjectReadingInstances; 2],
    positions: [ObjectEvaluationPosition; 2],
    names: &[(String, String)],
    c: &mut Control,
) -> Result<Family, ConstructionFailure> {
    let a = read(inputs, readings[0], positions[0], names, false, &[], c)?;
    let z = read(inputs, readings[1], positions[1], names, true, &[], c)?;
    let mut result = Family {
        applicable: a.application.zip(z.application).map(|(a, z)| a == z),
        equivalent: None,
        example: None,
        application_example: None,
        pending: a.pending.clone().or_else(|| z.pending.clone()),
        source: a,
        target: z,
        basis: vec![],
        systems: None,
    };
    let mut point = None;
    if result.applicable.is_some()
        && let (Some(a), Some(z)) = (&result.source.residual, &result.target.residual)
    {
        let at = a
            .numeric_parameter_terms(c)
            .map_err(invalid)?
            .ok_or_else(|| bad("元Lawの係数がない"))?;
        let zt = z
            .numeric_parameter_terms(c)
            .map_err(invalid)?
            .ok_or_else(|| bad("先Lawの係数がない"))?;
        result.basis =
            at.1.iter()
                .chain(&zt.1)
                .map(|(k, _)| k.clone())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
        let ground = result
            .basis
            .first()
            .map(|k| k.kind.ty())
            .unwrap_or_else(|| {
                if at.0.ty() == Type::Q || zt.0.ty() == Type::Q {
                    Type::Q
                } else {
                    Type::Z
                }
            });
        if result.basis.iter().any(|k| k.kind.ty() != ground) {
            result.pending = Some(pending(
                inputs.law().declarations[&readings[0].instances()[positions[0].instance]
                    .declaration()
                    .name]
                    .span,
                vec![],
            ));
            return Ok(result);
        }
        let sa = system(a, &result.basis, &ground, c).map_err(invalid)?;
        let sz = system(z, &result.basis, &ground, c).map_err(invalid)?;
        point = match outside(&sa, &sz, c).map_err(invalid)? {
            Some(point) => Some(point),
            None => outside(&sz, &sa, c).map_err(invalid)?,
        };
        result.equivalent = Some(point.is_none());
        result.systems = Some((sa, sz));
    }
    let mut points = point.into_iter().map(|p| (false, p)).collect::<Vec<_>>();
    if result.applicable == Some(false) {
        let point = result
            .basis
            .iter()
            .map(|axis| numeric::zero(&axis.kind.ty(), c))
            .collect::<Result<Vec<_>, _>>()
            .map_err(invalid)?;
        points.push((true, point));
    }
    for (application, point) in points {
        let row = &readings[0].instances()[positions[0].instance];
        let bindings =
            assignments(inputs, row, names, &result.basis, &point, c).map_err(invalid)?;
        let target_bindings = bindings
            .iter()
            .map(|(name, v)| {
                names
                    .iter()
                    .find(|(a, _)| a == name)
                    .map(|(_, z)| (z.clone(), v.clone()))
                    .ok_or_else(|| bad("数値Law反例の先引数がない"))
            })
            .collect::<Result<Vec<_>, _>>()?;
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
        let (left, right) = if application {
            (
                Scalar::Bool(a.application.ok_or_else(|| bad("元Law反例の適用が未決"))?),
                Scalar::Bool(z.application.ok_or_else(|| bad("先Law反例の適用が未決"))?),
            )
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
            if (left == numeric::zero(&left.ty(), c).map_err(invalid)?)
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
        if application {
            result.application_example = Some(example);
        } else {
            result.example = Some(example);
        }
    }
    Ok(result)
}
