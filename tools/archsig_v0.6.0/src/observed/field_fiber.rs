//! Q/Fp上の正確な行消去。全解・核・像と矛盾行の左零化子を保持する。
use super::{
    numeric,
    result::{Scalar, ValidationFailure},
};
use crate::control::{Checkpoint, Control};
use crate::{law::ast::BinOp, types::Type};
use num_traits::{One, Signed, Zero};
pub(super) type Matrix = Vec<Vec<Scalar>>;
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Fiber {
    pub reduced: Matrix,
    pub left: Matrix,
    pub transformed_rhs: Vec<Scalar>,
    pub pivots: Vec<usize>,
    pub particular: Option<Vec<Scalar>>,
    pub kernel: Matrix,
    pub image: Matrix,
    pub obstruction: Option<usize>,
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.clone()
        .checkpoint(Checkpoint::PrimitiveValuation)
        .map_err(Into::into)
}
fn op(a: &Scalar, operation: BinOp, b: &Scalar, c: &Control) -> Result<Scalar, ValidationFailure> {
    numeric::binary(operation, a, b, c)
}
fn inverse(value: &Scalar, c: &Control) -> Result<Scalar, ValidationFailure> {
    tick(c)?;
    numeric::check(value, c)?;
    let result = match value {
        Scalar::Q(n, d) if !n.is_zero() => {
            if n.is_negative() {
                Scalar::Q(-d, -n)
            } else {
                Scalar::Q(d.clone(), n.clone())
            }
        }
        Scalar::Fp { modulus, value } if !value.is_zero() => {
            let p: num_bigint::BigInt = modulus
                .parse()
                .map_err(|_| ValidationFailure::Internal("体の法を読めない".into()))?;
            let (mut a, mut b) = (p.clone(), value.clone());
            let (mut x, mut y) = (num_bigint::BigInt::zero(), num_bigint::BigInt::one());
            while !b.is_zero() {
                tick(c)?;
                let q = &a / &b;
                (a, b) = (b.clone(), a - &q * &b);
                (x, y) = (y.clone(), x - q * &y);
            }
            if !a.is_one() {
                return Err("体の係数が可逆でない".into());
            }
            Scalar::Fp {
                modulus: modulus.clone(),
                value: ((x % &p) + &p) % &p,
            }
        }
        _ => return Err("体の非零係数が必要".into()),
    };
    numeric::check(&result, c)?;
    Ok(result)
}
pub(super) fn solve(
    ty: &Type,
    a: &Matrix,
    n: usize,
    b: &[Scalar],
    c: &Control,
) -> Result<Fiber, ValidationFailure> {
    tick(c)?;
    if !matches!(ty, Type::Q | Type::Fp(_)) {
        return Err("体上の線形系の係数型がQ/Fpでない".into());
    }
    if a.len() != b.len() || a.iter().any(|row| row.len() != n) {
        return Err("体上の線形系の次元が違う".into());
    }
    for value in a.iter().flatten().chain(b) {
        tick(c)?;
        if value.ty() != *ty {
            return Err("体上の線形系の係数型が混在する".into());
        }
    }
    let zero = numeric::zero(ty, c)?;
    let one = numeric::literal("1", ty, c)?;
    let mut reduced = a.clone();
    let mut rhs = b.to_vec();
    let mut left = vec![];
    for i in 0..a.len() {
        tick(c)?;
        left.push(
            (0..a.len())
                .map(|j| if i == j { one.clone() } else { zero.clone() })
                .collect::<Vec<_>>(),
        );
    }
    let mut pivots = vec![];
    for col in 0..n {
        tick(c)?;
        let at = pivots.len();
        let mut pivot = None;
        for row in at..a.len() {
            tick(c)?;
            if reduced[row][col] != zero {
                pivot = Some(row);
                break;
            }
        }
        let Some(pivot) = pivot else { continue };
        reduced.swap(at, pivot);
        left.swap(at, pivot);
        rhs.swap(at, pivot);
        let divisor = inverse(&reduced[at][col], c)?;
        for x in &mut reduced[at] {
            *x = op(x, BinOp::Mul, &divisor, c)?;
        }
        for x in &mut left[at] {
            *x = op(x, BinOp::Mul, &divisor, c)?;
        }
        rhs[at] = op(&rhs[at], BinOp::Mul, &divisor, c)?;
        for row in 0..a.len() {
            tick(c)?;
            if row == at {
                continue;
            }
            let factor = reduced[row][col].clone();
            if factor == zero {
                continue;
            }
            for j in 0..n {
                reduced[row][j] = op(
                    &reduced[row][j],
                    BinOp::Sub,
                    &op(&factor, BinOp::Mul, &reduced[at][j], c)?,
                    c,
                )?;
            }
            for j in 0..a.len() {
                left[row][j] = op(
                    &left[row][j],
                    BinOp::Sub,
                    &op(&factor, BinOp::Mul, &left[at][j], c)?,
                    c,
                )?;
            }
            rhs[row] = op(
                &rhs[row],
                BinOp::Sub,
                &op(&factor, BinOp::Mul, &rhs[at], c)?,
                c,
            )?;
        }
        pivots.push(col);
    }
    let mut obstruction = None;
    for row in pivots.len()..a.len() {
        tick(c)?;
        if rhs[row] != zero {
            obstruction = Some(row);
            break;
        }
    }
    let particular = if obstruction.is_none() {
        let mut p = vec![zero.clone(); n];
        for (row, col) in pivots.iter().enumerate() {
            tick(c)?;
            p[*col] = rhs[row].clone();
        }
        Some(p)
    } else {
        None
    };
    let mut kernel = vec![vec![]; n];
    for col in 0..n {
        tick(c)?;
        if pivots.contains(&col) {
            continue;
        }
        let mut v = vec![zero.clone(); n];
        v[col] = one.clone();
        for (row, pivot) in pivots.iter().enumerate() {
            v[*pivot] = op(&zero, BinOp::Sub, &reduced[row][col], c)?;
        }
        for (row, x) in kernel.iter_mut().zip(v) {
            row.push(x);
        }
    }
    let mut image = vec![];
    for row in a {
        tick(c)?;
        image.push(pivots.iter().map(|i| row[*i].clone()).collect());
    }
    Ok(Fiber {
        reduced,
        left,
        transformed_rhs: rhs,
        pivots,
        particular,
        kernel,
        image,
        obstruction,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn quiet() -> Control {
        Control::unlimited()
    }
    fn q(n: i64) -> Scalar {
        Scalar::Q(n.into(), 1.into())
    }
    fn dot(a: &[Scalar], b: &[Scalar], ty: &Type, c: &Control) -> Scalar {
        a.iter()
            .zip(b)
            .fold(numeric::zero(ty, c).unwrap(), |sum, (x, y)| {
                op(&sum, BinOp::Add, &op(x, BinOp::Mul, y, c).unwrap(), c).unwrap()
            })
    }
    fn verify(ty: &Type, a: &Matrix, b: &[Scalar], n: usize, f: &Fiber, c: &Control) {
        let zero = numeric::zero(ty, c).unwrap();
        for (i, left) in f.left.iter().enumerate() {
            for j in 0..n {
                assert_eq!(
                    dot(
                        left,
                        &a.iter().map(|row| row[j].clone()).collect::<Vec<_>>(),
                        ty,
                        c
                    ),
                    f.reduced[i][j]
                );
            }
            assert_eq!(dot(left, b, ty, c), f.transformed_rhs[i]);
        }
        if let Some(p) = &f.particular {
            for (row, rhs) in a.iter().zip(b) {
                assert_eq!(dot(row, p, ty, c), *rhs);
            }
        }
        for j in 0..n - f.pivots.len() {
            let v = f
                .kernel
                .iter()
                .map(|row| row[j].clone())
                .collect::<Vec<_>>();
            for row in a {
                assert_eq!(dot(row, &v, ty, c), zero);
            }
        }
        if let Some(i) = f.obstruction {
            for j in 0..n {
                assert_eq!(
                    dot(
                        &f.left[i],
                        &a.iter().map(|row| row[j].clone()).collect::<Vec<_>>(),
                        ty,
                        c
                    ),
                    zero
                );
            }
            assert_ne!(dot(&f.left[i], b, ty, c), zero);
        }
        for (row, original) in f.image.iter().zip(a) {
            assert_eq!(
                *row,
                f.pivots
                    .iter()
                    .map(|i| original[*i].clone())
                    .collect::<Vec<_>>()
            );
        }
    }
    #[test]
    fn exact_field_elimination_keeps_fraction_kernel_image_and_left_obstruction() {
        let c = quiet();
        for ty in [Type::Q, Type::Fp("5".into()), Type::Fp("2".into())] {
            let v = |n: &str| numeric::literal(n, &ty, &c).unwrap();
            for (a, b, n, rank, exists) in [
                (
                    vec![vec![v("1"), v("1")], vec![v("1"), v("0")]],
                    vec![v("1"), v("0")],
                    2,
                    2,
                    true,
                ),
                (vec![vec![v("1"), v("1"), v("0")]], vec![v("1")], 3, 1, true),
                (
                    vec![vec![v("1")], vec![v("1")]],
                    vec![v("0"), v("1")],
                    1,
                    1,
                    false,
                ),
                (vec![], vec![], 2, 0, true),
                (vec![vec![]], vec![v("1")], 0, 0, false),
            ] {
                let f = solve(&ty, &a, n, &b, &c).unwrap();
                assert_eq!(f.pivots.len(), rank);
                assert_eq!(f.particular.is_some(), exists);
                assert_eq!(f.obstruction.is_some(), !exists);
                verify(&ty, &a, &b, n, &f, &c);
            }
        }
        let a = vec![vec![q(1), q(1)], vec![q(1), q(-1)]];
        let f = solve(&Type::Q, &a, 2, &[q(1), q(0)], &c).unwrap();
        assert_eq!(f.particular, Some(vec![Scalar::Q(1.into(), 2.into()); 2]));
        verify(&Type::Q, &a, &[q(1), q(0)], 2, &f, &c);
    }
}
