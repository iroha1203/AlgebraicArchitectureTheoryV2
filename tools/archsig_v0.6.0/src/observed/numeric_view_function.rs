//! 元viewの数値引数を、既存の記号評価で全域のアフィン関数として読む。
use super::*;
use crate::construction::{
    ConstructionFailure,
    readings::{InstanceApplication, ObjectReadingInstances},
};
use crate::observed::{affine, object_evaluate::ObjectDomain, term::affine::Value};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum Reading {
    Outside,
    Value(Function),
    Unknown(Vec<Fact>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Function {
    coordinates: Vec<Coordinate>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Coordinate {
    component: Vec<usize>,
    constant: Scalar,
    coefficients: Vec<((String, usize), Scalar)>,
}
fn invalid(e: ValidationFailure) -> ConstructionFailure {
    match e {
        ValidationFailure::Stop(s) => s.into(),
        e => ConstructionFailure::Inconsistent(format!("数値viewの元式: {e:?}")),
    }
}
fn function(
    value: &Value,
    axes: &[(affine::Parameter, (String, usize))],
    c: &Control,
) -> Result<Result<Function, Vec<Fact>>, ValidationFailure> {
    enum Part<'a> {
        Symbolic(&'a Value),
        Known(&'a Scalar),
    }
    let mut pending = vec![(vec![], Part::Symbolic(value))];
    let mut coordinates = vec![];
    while let Some((path, part)) = pending.pop() {
        c.clone()
            .checkpoint(Checkpoint::ObjectViewTransportFamily)?;
        let (constant, terms) = match part {
            Part::Symbolic(Value::Known(value)) => {
                pending.push((path, Part::Known(value)));
                continue;
            }
            Part::Known(Scalar::Tuple(items)) => {
                for (index, item) in items.iter().enumerate() {
                    c.clone()
                        .checkpoint(Checkpoint::ObjectViewTransportFamily)?;
                    let mut child = path.clone();
                    child.push(index);
                    pending.push((child, Part::Known(item)));
                }
                continue;
            }
            Part::Symbolic(Value::Tuple(items)) => {
                for (index, item) in items.iter().enumerate() {
                    c.clone()
                        .checkpoint(Checkpoint::ObjectViewTransportFamily)?;
                    let mut child = path.clone();
                    child.push(index);
                    pending.push((child, Part::Symbolic(item)));
                }
                continue;
            }
            Part::Known(value @ (Scalar::Z(_) | Scalar::Q(..))) => (value.clone(), vec![]),
            Part::Symbolic(Value::Number(form)) => {
                let Some(value) = form.parameter_coordinates(c)? else {
                    return Ok(Err(form.missing_facts()));
                };
                value
            }
            _ => return Ok(Err(vec![])),
        };
        let mut coefficients = vec![];
        for (parameter, coefficient) in terms {
            c.clone()
                .checkpoint(Checkpoint::ObjectViewTransportFamily)?;
            let key = axes
                .iter()
                .find(|(axis, _)| axis == &parameter)
                .map(|(_, key)| key.clone())
                .ok_or("数値viewの係数に元引数の軸がない")?;
            coefficients.push((key, coefficient));
        }
        coefficients.sort_by(|a, b| a.0.cmp(&b.0));
        coordinates.push(Coordinate {
            component: path,
            constant,
            coefficients,
        });
    }
    coordinates.sort_by(|a, b| a.component.cmp(&b.component));
    Ok(Ok(Function { coordinates }))
}
pub(in crate::observed) fn read(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    object: usize,
    instance: usize,
    names: &[(String, String)],
    target: bool,
    c: &mut Control,
) -> Result<Reading, ConstructionFailure> {
    let row = readings
        .instances()
        .get(instance)
        .ok_or_else(|| ConstructionFailure::Inconsistent("数値viewのinstanceがない".into()))?;
    match row.applications().get(object) {
        Some(InstanceApplication::NotApplicable) => return Ok(Reading::Outside),
        Some(InstanceApplication::Applicable { conditions }) if conditions.is_empty() => {}
        Some(_) => return Ok(Reading::Unknown(vec![])),
        None => {
            return Err(ConstructionFailure::Inconsistent(
                "数値viewの対象別適用がない".into(),
            ));
        }
    }
    let declaration = inputs
        .law()
        .declarations
        .get(&row.declaration().name)
        .ok_or_else(|| ConstructionFailure::Inconsistent("数値viewの宣言がない".into()))?;
    let crate::law::model::Signature::View { params, body, .. } = &declaration.signature else {
        return Err(ConstructionFailure::InvalidSelection(
            "数値viewを選択する".into(),
        ));
    };
    let mut env = Environment::new(inputs, c).map_err(ConstructionFailure::from)?;
    env.object = Some(Arc::new(
        ObjectDomain::from_readings(inputs, readings, object, c).map_err(invalid)?,
    ));
    env.object_instance = Some(row);
    let mut bindings = vec![];
    for binding in row.bindings() {
        c.checkpoint(Checkpoint::ObjectViewTransportFamily)
            .map_err(ConstructionFailure::from)?;
        bindings.push((
            binding.parameter().name.clone(),
            Scalar::Subject {
                snapshot: binding.subject().snapshot.clone(),
                subject: binding.subject().subject.clone(),
                entity: match &binding.parameter().ty.erase() {
                    Type::Ref(entity) => entity.clone(),
                    _ => {
                        return Err(ConstructionFailure::Inconsistent(
                            "数値viewの固定束縛が参照でない".into(),
                        ));
                    }
                },
            },
        ));
    }
    let (variables, _) =
        numeric_parameters::law_variables(&env, params, &bindings).map_err(invalid)?;
    let mut axes = vec![];
    for p in params
        .iter()
        .filter(|p| !bindings.iter().any(|(name, _)| name == &p.name))
    {
        c.checkpoint(Checkpoint::ObjectViewTransportFamily)
            .map_err(ConstructionFailure::from)?;
        let name = if target {
            names
                .iter()
                .find(|(_, z)| z == &p.name)
                .map(|(a, _)| a.clone())
                .ok_or_else(|| {
                    ConstructionFailure::Inconsistent("数値viewの引数対応がない".into())
                })?
        } else {
            p.name.clone()
        };
        for (index, axis) in numeric_parameters::axes(p, env.context.get().unwrap_or_default(), c)
            .map_err(invalid)?
            .into_iter()
            .enumerate()
        {
            axes.push((axis, (name.clone(), index)));
        }
    }
    let value = env
        .scoped_ast(*body, &variables, &Scope::default(), &declaration.reading)
        .map_err(invalid)?;
    if value.condition_failed {
        return Ok(Reading::Outside);
    }
    if value.condition_pending {
        return Ok(Reading::Unknown(vec![]));
    }
    let symbolic = value
        .known_value
        .map(Value::Known)
        .or_else(|| value.affine.map(|v| Value::Number(*v)))
        .or_else(|| value.symbolic.map(|v| *v));
    let Some(value) = symbolic else {
        return Ok(Reading::Unknown(vec![]));
    };
    Ok(match function(&value, &axes, c).map_err(invalid)? {
        Ok(function) => Reading::Value(function),
        Err(missing) => Reading::Unknown(missing),
    })
}
