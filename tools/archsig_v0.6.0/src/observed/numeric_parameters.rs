//! 数値引数の独立軸と元の引数形を、既存の記号評価へ接続する。
use super::*;
use crate::{law::model::Param, observed::affine};
// 同じ係数型の葉を、元のTuple順に独立なscalar軸として読む。
fn numeric_shape(ty: &Type) -> Option<(Type, usize)> {
    let mut pending = vec![ty];
    let mut kind = None;
    let mut width = 0usize;
    while let Some(ty) = pending.pop() {
        match ty {
            Type::Z | Type::Q => {
                if kind.as_ref().is_some_and(|kind| kind != ty) {
                    return None;
                }
                kind = Some(ty.clone());
                width = width.checked_add(1)?;
            }
            Type::Tuple(items) if !items.is_empty() => pending.extend(items.iter().rev()),
            _ => return None,
        }
    }
    Some((kind?, width))
}
pub(in crate::observed) fn numeric_width(ty: &Type) -> Option<usize> {
    numeric_shape(ty).map(|(_, width)| width)
}
// 同じ元binderの数値成分を、既存の記号と同じ名前・順序で得る。
pub(in crate::observed) fn axes(
    p: &Param,
    context: super::super::call::Context,
    c: &Control,
) -> Result<Vec<affine::Parameter>, ValidationFailure> {
    let (kind, width) = numeric_shape(&p.ty).ok_or("数値引数の成分型がない")?;
    let kind = if kind == Type::Z {
        affine::NumberType::Z
    } else {
        affine::NumberType::Q
    };
    let mut out = vec![];
    for index in 0..width {
        c.clone().checkpoint(Checkpoint::FiniteIteration)?;
        out.push(affine::Parameter {
            binder: p.span,
            context,
            kind,
            name: if matches!(p.ty, Type::Tuple(_)) {
                format!("{}.{index}", p.name)
            } else {
                p.name.clone()
            },
        });
    }
    Ok(out)
}
// 軸の列を型の形へ戻す。記号式と反例で同じ葉順を使う。
pub(in crate::observed) fn restore<T>(
    ty: &Type,
    c: &Control,
    leaf: &mut impl FnMut() -> Result<T, ValidationFailure>,
    tuple: &impl Fn(Vec<T>) -> T,
) -> Result<T, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        c.clone().checkpoint(Checkpoint::FiniteIteration)?;
        match ty {
            Type::Tuple(items) => {
                let mut parts = vec![];
                for item in items {
                    parts.push(restore(item, c, leaf, tuple)?);
                }
                Ok(tuple(parts))
            }
            Type::Z | Type::Q => leaf(),
            _ => Err("数値引数の復元型が違う".into()),
        }
    })
}
// helperの実引数も、元の成分式へ同じ反例を代入して復元する。
pub(in crate::observed) fn substitute_value(
    value: &super::super::term::affine::Value,
    assignment: &[(affine::Parameter, Scalar)],
    c: &Control,
) -> Result<Option<Scalar>, ValidationFailure> {
    use super::super::term::affine::Value;
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        c.clone().checkpoint(Checkpoint::FiniteIteration)?;
        match value {
            Value::Known(value) => Ok(Some(value.clone())),
            Value::Number(form) => affine::substitute_parameters(form, assignment, c)?.value(c),
            Value::Tuple(items) => {
                let mut out = vec![];
                for item in items {
                    let Some(value) = substitute_value(item, assignment, c)? else {
                        return Ok(None);
                    };
                    out.push(value);
                }
                Ok(Some(Scalar::Tuple(out)))
            }
            _ => Ok(None),
        }
    })
}
pub(in crate::observed) fn tuple_variables(
    e: &Environment<'_>,
    params: &[Param],
    variables: &mut BTreeMap<String, SourceValue>,
) -> Result<(), ValidationFailure> {
    use crate::observed::term::affine::Value;
    for p in params {
        if !matches!(p.ty, Type::Tuple(_)) || !variables.contains_key(&format!("{}.0", p.name)) {
            continue;
        }
        let Some(width) = numeric_width(&p.ty) else {
            continue;
        };
        let mut parts = vec![];
        let mut aggregate = variables[&format!("{}.0", p.name)].clone();
        aggregate.support.clear();
        for index in 0..width {
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
        let mut parts = parts.into_iter();
        let symbolic = restore(
            &p.ty,
            &e.control,
            &mut || parts.next().ok_or_else(|| "数値Tupleの成分がない".into()),
            &Value::Tuple,
        )?;
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
        if matches!(p.ty, Type::Tuple(_))
            && numeric_width(&p.ty).is_some()
            && !bindings.iter().any(|(name, _)| *name == p.name)
        {
            for axis in axes(p, e.context.get().unwrap_or_default(), &e.control)? {
                flat.push(Param {
                    name: axis.name,
                    ty: axis.kind.ty(),
                    span: axis.binder,
                });
            }
            continue;
        }
        flat.push(p.clone());
    }
    let (mut variables, axes) = change_affine::law_variables(e, &flat, bindings)?;
    tuple_variables(e, params, &mut variables)?;
    Ok((variables, axes))
}

pub(in crate::observed) fn coefficient_type(ty: &Type) -> Option<Type> {
    numeric_shape(ty).map(|(kind, _)| kind)
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
    let mut coordinates = coordinates.iter();
    restore(
        &parameter.ty,
        c,
        &mut || {
            coordinates
                .next()
                .cloned()
                .ok_or_else(|| "数値反例の座標がない".into())
        },
        &Scalar::Tuple,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::control::{Limits, Usage};

    #[test]
    fn nested_numeric_point_preserves_shape_and_later_parameter_offsets() {
        for kind in [Type::Z, Type::Q] {
            let c = Control::new(Limits::default(), |_| Usage::default());
            let nested = Type::Tuple(vec![
                kind.clone(),
                Type::Tuple(vec![
                    kind.clone(),
                    Type::Tuple(vec![kind.clone(), kind.clone()]),
                ]),
            ]);
            let params: Vec<_> = [
                nested,
                kind.clone(),
                Type::Tuple(vec![kind.clone(), kind.clone()]),
            ]
            .into_iter()
            .enumerate()
            .map(|(index, ty)| Param {
                name: format!("p{index}"),
                ty,
                span: (index, index + 1),
            })
            .collect();
            let n = |v: i32| match kind {
                Type::Z => Scalar::Z(v.into()),
                _ => Scalar::Q(v.into(), 1.into()),
            };
            let point: Vec<_> = (1i32..=7).map(n).collect();
            assert_eq!(
                point_value(&params, &params[0], &point, &c).unwrap(),
                Scalar::Tuple(vec![
                    n(1),
                    Scalar::Tuple(vec![n(2), Scalar::Tuple(vec![n(3), n(4)])])
                ])
            );
            assert_eq!(point_value(&params, &params[1], &point, &c).unwrap(), n(5));
            assert_eq!(
                point_value(&params, &params[2], &point, &c).unwrap(),
                Scalar::Tuple(vec![n(6), n(7)])
            );
            assert!(point_value(&params, &params[2], &point[..6], &c).is_err());
        }
    }

    #[test]
    fn nested_numeric_axes_keep_mixed_and_nonnumeric_leaves_out() {
        for leaf in [Type::Q, Type::Bool, Type::Tuple(vec![])] {
            let ty = Type::Tuple(vec![Type::Z, Type::Tuple(vec![Type::Z, leaf])]);
            assert_eq!(numeric_width(&ty), None);
            assert_eq!(coefficient_type(&ty), None);
        }
    }
}
