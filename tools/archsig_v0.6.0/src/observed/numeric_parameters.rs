//! 数値引数の独立軸と元の引数形を、既存の記号評価へ接続する。
use super::*;
use crate::{law::model::Param, observed::affine};
// 最小の複合数値域として、平坦で同種のTupleだけをscalar軸へ展開する。
pub(in crate::observed) fn numeric_width(ty: &Type) -> Option<usize> {
    match ty {
        Type::Z | Type::Q => Some(1),
        Type::Tuple(items)
            if !items.is_empty()
                && matches!(items[0], Type::Z | Type::Q)
                && items.iter().all(|ty| *ty == items[0]) =>
        {
            Some(items.len())
        }
        _ => None,
    }
}
pub(in crate::observed) fn tuple_variables(
    e: &Environment<'_>,
    params: &[Param],
    variables: &mut BTreeMap<String, SourceValue>,
) -> Result<(), ValidationFailure> {
    use crate::observed::term::affine::Value;
    for p in params {
        if !matches!(p.ty, Type::Tuple(_))
            || numeric_width(&p.ty).is_none()
            || !variables.contains_key(&format!("{}.0", p.name))
        {
            continue;
        }
        let mut parts = vec![];
        let mut aggregate = variables[&format!("{}.0", p.name)].clone();
        aggregate.support.clear();
        for index in 0..numeric_width(&p.ty).ok_or("数値Tupleの幅がない")? {
            e.tick()?;
            let v = variables
                .get(&format!("{}.{index}", p.name))
                .ok_or("数値Tupleの軸がない")?;
            aggregate.scope.merge(&v.scope);
            aggregate.support.extend(v.support.iter().cloned());
            aggregate.condition_failed |= v.condition_failed;
            aggregate.condition_pending |= v.condition_pending;
            parts.push(if let Some(form) = &v.affine {
                Value::Number(form.as_ref().clone())
            } else if let Some(value) = &v.known_value {
                Value::Known(value.clone())
            } else {
                return Err("数値Tupleの成分がない".into());
            });
        }
        let symbolic = Value::Tuple(parts);
        aggregate.known_value = symbolic.known(&e.control)?;
        aggregate.scalar_scope = aggregate
            .known_value
            .as_ref()
            .map(|_| aggregate.scope.clone());
        aggregate.affine = None;
        aggregate.symbolic = Some(Box::new(symbolic));
        aggregate.comparison = None;
        variables.insert(p.name.clone(), aggregate);
    }
    Ok(())
}
pub(in crate::observed) fn law_variables(
    e: &Environment<'_>,
    params: &[Param],
    bindings: &[(String, Scalar)],
) -> Result<(BTreeMap<String, SourceValue>, Vec<affine::Parameter>), ValidationFailure> {
    let mut flat = vec![];
    for p in params {
        e.tick()?;
        if let Type::Tuple(items) = &p.ty {
            if numeric_width(&p.ty).is_some() && !bindings.iter().any(|(name, _)| *name == p.name) {
                for (index, ty) in items.iter().enumerate() {
                    e.tick()?;
                    flat.push(Param {
                        name: format!("{}.{index}", p.name),
                        ty: ty.clone(),
                        span: p.span,
                    });
                }
                continue;
            }
        }
        flat.push(p.clone());
    }
    let (mut variables, axes) = change_affine::law_variables(e, &flat, bindings)?;
    tuple_variables(e, params, &mut variables)?;
    Ok((variables, axes))
}

pub(in crate::observed) fn coefficient_type(ty: &Type) -> Option<Type> {
    numeric_width(ty)?;
    Some(match ty {
        Type::Tuple(items) => items[0].clone(),
        _ => ty.clone(),
    })
}
pub(in crate::observed) fn point_value(
    params: &[Param],
    parameter: &Param,
    point: &[Scalar],
    c: &Control,
) -> Result<Scalar, ValidationFailure> {
    let mut offset = 0;
    let mut found = false;
    for p in params {
        c.clone().checkpoint(Checkpoint::FiniteIteration)?;
        if p == parameter {
            found = true;
            break;
        }
        offset += numeric_width(&p.ty).ok_or("数値反例の引数型が違う")?;
    }
    if !found {
        return Err("数値反例の元引数がない".into());
    }
    let width = numeric_width(&parameter.ty).ok_or("数値反例の引数幅がない")?;
    let coordinates = point
        .get(offset..offset + width)
        .ok_or("数値反例の座標がない")?;
    Ok(if matches!(parameter.ty, Type::Tuple(_)) {
        Scalar::Tuple(coordinates.to_vec())
    } else {
        coordinates[0].clone()
    })
}
