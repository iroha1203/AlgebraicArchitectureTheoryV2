//! Zの格子像とQの線形像を保ったまま商へ渡す係数算術。
use super::*;
use crate::observed::{field_fiber, integer_fiber};
use num_traits::{One, Zero};
fn vector(v: &[num_bigint::BigInt]) -> Vec<Scalar> {
    v.iter().cloned().map(Scalar::Z).collect()
}
fn matrix(m: &integer_fiber::Matrix) -> Matrix {
    m.iter().map(|row| vector(row)).collect()
}
pub(in crate::observed) struct Input {
    pub ty: Type,
    pub parameter_count: usize,
    pub axes: Vec<affine::Parameter>,
    pub particular: Option<Vec<Scalar>>,
    pub kernel: Matrix,
    pub guard_origin: Option<Vec<Scalar>>,
    pub guard_kernel: Matrix,
    pub guard_dimensions: usize,
    pub slots: Vec<Fact>,
    pub action: Matrix,
    pub offset: Vec<Scalar>,
}
impl Input {
    pub fn from_search(
        search: &change_search::Search,
        c: &Control,
    ) -> Result<Self, ValidationFailure> {
        if let Some(x) = &search.rational {
            return Ok(Self {
                ty: Type::Q,
                parameter_count: x.parameter_count,
                axes: x.axes.clone(),
                particular: x.particular.clone(),
                kernel: x.kernel.clone(),
                guard_origin: x.guard_fiber.particular.clone(),
                guard_kernel: x.guard_fiber.kernel.clone(),
                guard_dimensions: x.parameter_count - x.guard_fiber.pivots.len(),
                slots: x.slots.clone(),
                action: x.action.clone(),
                offset: x.offset.clone(),
            });
        }
        let x = search.linear.as_ref().ok_or("商の線形表示がない")?;
        let n = x.parameter_count;
        let (guard_origin, guard_kernel, guard_dimensions) = if x.candidates_empty {
            (None, vec![vec![]; n], 0)
        } else if let Some(g) = &x.guard {
            (
                g.fiber.particular.as_ref().map(|v| vector(v)),
                matrix(&g.fiber.kernel),
                n - g.fiber.rank,
            )
        } else {
            let mut identity = vec![];
            for i in 0..n {
                c.clone().checkpoint(Checkpoint::Quotient)?;
                let mut row = vec![Scalar::Z(num_bigint::BigInt::zero()); n];
                row[i] = Scalar::Z(num_bigint::BigInt::one());
                identity.push(row);
            }
            (
                Some(vec![Scalar::Z(num_bigint::BigInt::zero()); n]),
                identity,
                n,
            )
        };
        Ok(Self {
            ty: Type::Z,
            parameter_count: n,
            axes: x.axes.clone(),
            particular: x.particular.as_ref().map(|v| vector(v)),
            kernel: matrix(&x.kernel),
            guard_origin,
            guard_kernel,
            guard_dimensions,
            slots: x.slots.clone(),
            action: matrix(&x.action),
            offset: vector(&x.offset),
        })
    }
}
pub(in crate::observed) fn coordinates(
    f: &affine::Form,
    axes: &[affine::Parameter],
    ty: &Type,
    c: &Control,
) -> Result<Option<(Scalar, Vec<Scalar>)>, ValidationFailure> {
    match ty {
        Type::Z => Ok(f
            .integer_coordinates(axes, c)?
            .map(|(a, b)| (Scalar::Z(a), vector(&b)))),
        Type::Q => f.rational_coordinates(axes, c),
        _ => Err("商の係数型がZ/Qでない".into()),
    }
}
pub(in crate::observed) fn add_product(
    sum: &Scalar,
    a: &Scalar,
    b: &Scalar,
    c: &Control,
) -> Result<Scalar, ValidationFailure> {
    numeric::binary(BinOp::Add, sum, &numeric::binary(BinOp::Mul, a, b, c)?, c)
}
pub(in crate::observed) fn multiply(
    ty: &Type,
    a: &Matrix,
    b: &Matrix,
    cols: usize,
    c: &Control,
) -> Result<Matrix, ValidationFailure> {
    if a.iter().any(|r| r.len() != b.len()) || b.iter().any(|r| r.len() != cols) {
        return Err("商の行列積の次元が違う".into());
    }
    let mut result = vec![];
    for row in a {
        let mut out = vec![];
        for j in 0..cols {
            let mut sum = numeric::zero(ty, c)?;
            for (x, r) in row.iter().zip(b) {
                sum = add_product(&sum, x, &r[j], c)?;
            }
            out.push(sum);
        }
        result.push(out);
    }
    Ok(result)
}
pub(in crate::observed) struct Fiber {
    pub rank: usize,
    pub kernel: Matrix,
    pub image: Matrix,
    pub lifts: Matrix,
}
pub(in crate::observed) fn fiber(
    ty: &Type,
    a: &Matrix,
    n: usize,
    c: &mut Control,
) -> Result<Fiber, ValidationFailure> {
    if *ty == Type::Z {
        let a = a
            .iter()
            .map(|row| {
                row.iter()
                    .map(|x| {
                        if let Scalar::Z(x) = x {
                            Ok(x.clone())
                        } else {
                            Err(ValidationFailure::from("整数商の係数がZでない"))
                        }
                    })
                    .collect()
            })
            .collect::<Result<integer_fiber::Matrix, _>>()?;
        let f = integer_fiber::solve(&a, n, &vec![num_bigint::BigInt::zero(); a.len()], c)?;
        let basis = integer_fiber::multiply(&a, &f.right, n, c)?;
        return Ok(Fiber {
            rank: f.rank,
            kernel: matrix(&f.kernel),
            image: matrix(&basis.iter().map(|r| r[..f.rank].to_vec()).collect()),
            lifts: matrix(&f.right.iter().map(|r| r[..f.rank].to_vec()).collect()),
        });
    }
    let f = field_fiber::solve(ty, a, n, &vec![numeric::zero(ty, c)?; a.len()], c)?;
    let rank = f.pivots.len();
    let mut lifts = vec![vec![numeric::zero(ty, c)?; rank]; n];
    for (j, i) in f.pivots.iter().enumerate() {
        lifts[*i][j] = numeric::literal("1", ty, c)?;
    }
    Ok(Fiber {
        rank,
        kernel: f.kernel,
        image: f.image,
        lifts,
    })
}

pub(in crate::observed) fn view_type(
    ty: &Type,
    coefficient: &Type,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        c.clone().checkpoint(Checkpoint::Quotient)?;
        if ty == coefficient {
            return Ok(true);
        }
        if let Type::Tuple(items) = ty {
            for item in items {
                if !view_type(item, coefficient, c)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        Ok(false)
    })
}
pub(in crate::observed) fn view_coordinates(
    value: &crate::observed::term::affine::Value,
    axes: &[affine::Parameter],
    ty: &Type,
    c: &Control,
) -> Result<Option<(Vec<Scalar>, Matrix)>, ValidationFailure> {
    use crate::observed::term::affine::Value;
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        c.clone().checkpoint(Checkpoint::Quotient)?;
        let items = match value {
            Value::Tuple(xs) => Some(xs.clone()),
            Value::Known(Scalar::Tuple(xs)) => Some(xs.iter().cloned().map(Value::Known).collect()),
            _ => None,
        };
        if let Some(items) = items {
            let mut offsets = vec![];
            let mut matrix = vec![];
            for item in items {
                let Some((o, m)) = view_coordinates(&item, axes, ty, c)? else {
                    return Ok(None);
                };
                offsets.extend(o);
                matrix.extend(m);
            }
            return Ok(Some((offsets, matrix)));
        }
        let Some(form) = value.number(c)? else {
            return Ok(None);
        };
        Ok(coordinates(&form, axes, ty, c)?.map(|(o, m)| (vec![o], vec![m])))
    })
}
pub(in crate::observed) fn view_value(
    ty: &Type,
    flat: &[Scalar],
    c: &Control,
) -> Result<Scalar, ValidationFailure> {
    fn read(
        ty: &Type,
        flat: &[Scalar],
        at: &mut usize,
        c: &Control,
    ) -> Result<Scalar, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            c.clone().checkpoint(Checkpoint::Quotient)?;
            if let Type::Tuple(items) = ty {
                return Ok(Scalar::Tuple(
                    items
                        .iter()
                        .map(|t| read(t, flat, at, c))
                        .collect::<Result<_, _>>()?,
                ));
            }
            let value = flat.get(*at).ok_or("商のView座標が足りない")?;
            if value.ty() != *ty {
                return Err("商のView座標の型が違う".into());
            }
            *at += 1;
            Ok(value.clone())
        })
    }
    let mut at = 0;
    let value = read(ty, flat, &mut at, c)?;
    if at != flat.len() {
        return Err("商のView座標が余る".into());
    }
    Ok(value)
}
