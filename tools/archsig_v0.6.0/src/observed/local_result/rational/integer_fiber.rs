//! 体上の消去を共通局所計算の基底変換へ接続する。
use super::*;
use num_traits::One;
pub(in crate::observed::local_result) type Matrix = Vec<Vec<Z>>;
#[derive(Clone, Debug)]
pub(in crate::observed::local_result) struct Fiber {
    pub diagonal: Matrix,
    pub left: Matrix,
    pub right: Matrix,
    pub transformed_rhs: Vec<Z>,
    pub rank: usize,
    pub particular: Option<Vec<Z>>,
    pub kernel: Matrix,
    pub obstruction: Option<usize>,
}
pub(in crate::observed::local_result) fn scalars(
    a: &Matrix,
) -> crate::observed::field_fiber::Matrix {
    a.iter()
        .map(|r| r.iter().map(Z::scalar).collect())
        .collect()
}
pub(in crate::observed::local_result) fn vector(a: &[Scalar]) -> Result<Vec<Z>, ValidationFailure> {
    a.iter().map(Z::from_scalar).collect()
}
pub(in crate::observed::local_result) fn matrix(
    a: &crate::observed::field_fiber::Matrix,
) -> Result<Matrix, ValidationFailure> {
    a.iter().map(|r| vector(r)).collect()
}
pub(in crate::observed::local_result) fn solve(
    a: &Matrix,
    n: usize,
    b: &[Z],
    c: &Control,
) -> Result<Fiber, ValidationFailure> {
    let f = crate::observed::field_fiber::solve(
        &Type::Q,
        &scalars(a),
        n,
        &b.iter().map(Z::scalar).collect::<Vec<_>>(),
        c,
    )?;
    let rank = f.pivots.len();
    let kernel = matrix(&f.kernel)?;
    let mut right = vec![vec![Z::zero(); n]; n];
    for (j, p) in f.pivots.iter().enumerate() {
        right[*p][j] = Z::one();
    }
    for i in 0..n {
        for j in 0..n - rank {
            right[i][rank + j] = kernel[i][j].clone();
        }
    }
    let mut diagonal = vec![vec![Z::zero(); n]; a.len()];
    for i in 0..rank {
        diagonal[i][i] = Z::one();
    }
    Ok(Fiber {
        diagonal,
        left: matrix(&f.left)?,
        right,
        transformed_rhs: vector(&f.transformed_rhs)?,
        rank,
        particular: f.particular.as_ref().map(|v| vector(v)).transpose()?,
        kernel,
        obstruction: f.obstruction,
    })
}
pub(in crate::observed::local_result) fn multiply(
    a: &Matrix,
    b: &Matrix,
    cols: usize,
    c: &Control,
) -> Result<Matrix, ValidationFailure> {
    if a.iter().any(|r| r.len() != b.len()) || b.iter().any(|r| r.len() != cols) {
        return Err("有理行列の積の次元が異なる".into());
    }
    let mut out = vec![vec![Z::zero(); cols]; a.len()];
    for (i, row) in a.iter().enumerate() {
        for j in 0..cols {
            for (k, x) in row.iter().enumerate() {
                c.checkpoint(crate::control::Checkpoint::Localize)?;
                let product = crate::observed::numeric::binary(
                    BinOp::Mul,
                    &x.scalar(),
                    &b[k][j].scalar(),
                    c,
                )?;
                let sum =
                    crate::observed::numeric::binary(BinOp::Add, &out[i][j].scalar(), &product, c)?;
                out[i][j] = Z::from_scalar(&sum)?;
            }
        }
    }
    Ok(out)
}
