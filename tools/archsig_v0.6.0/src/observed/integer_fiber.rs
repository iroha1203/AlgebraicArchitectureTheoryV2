//! 整数行列を左右の可逆な整数基本変形で対角化し、全fiberを得る。
use super::result::ValidationFailure;
use crate::control::{Checkpoint, Control};
use num_bigint::BigInt as Z;
use num_traits::{One, Signed, Zero};

pub(super) type Matrix = Vec<Vec<Z>>;
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Fiber {
    pub diagonal: Matrix,
    pub left: Matrix,
    pub right: Matrix,
    pub transformed_rhs: Vec<Z>,
    pub rank: usize,
    pub particular: Option<Vec<Z>>,
    /// 各列が元parameter座標の整数核の基底。
    pub kernel: Matrix,
    pub obstruction: Option<usize>,
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.clone()
        .checkpoint(Checkpoint::PrimitiveValuation)
        .map_err(Into::into)
}
fn identity(n: usize, c: &Control) -> Result<Matrix, ValidationFailure> {
    let mut result = vec![];
    for i in 0..n {
        tick(c)?;
        let mut row = vec![Z::zero(); n];
        row[i] = Z::one();
        result.push(row);
    }
    Ok(result)
}
fn add_row(
    m: &mut Matrix,
    dst: usize,
    src: usize,
    q: &Z,
    c: &Control,
) -> Result<(), ValidationFailure> {
    for j in 0..m[dst].len() {
        tick(c)?;
        let value = &m[src][j] * q;
        m[dst][j] += value;
    }
    Ok(())
}
fn add_col(
    m: &mut Matrix,
    dst: usize,
    src: usize,
    q: &Z,
    c: &Control,
) -> Result<(), ValidationFailure> {
    for row in m {
        tick(c)?;
        let value = &row[src] * q;
        row[dst] += value;
    }
    Ok(())
}
pub(super) fn multiply(
    a: &Matrix,
    b: &Matrix,
    cols: usize,
    c: &Control,
) -> Result<Matrix, ValidationFailure> {
    if a.iter().any(|r| r.len() != b.len()) || b.iter().any(|r| r.len() != cols) {
        return Err("整数行列の積の次元が違う".into());
    }
    let mut out = vec![];
    for row in a {
        let mut result = vec![];
        for j in 0..cols {
            let mut value = Z::zero();
            for (x, brow) in row.iter().zip(b) {
                tick(c)?;
                value += x * &brow[j];
            }
            result.push(value);
        }
        out.push(result);
    }
    tick(c)?;
    Ok(out)
}
pub(super) fn solve(
    a: &Matrix,
    cols: usize,
    rhs: &[Z],
    c: &Control,
) -> Result<Fiber, ValidationFailure> {
    tick(c)?;
    if a.len() != rhs.len() || a.iter().any(|r| r.len() != cols) {
        return Err("整数系の行列・右辺の次元が違う".into());
    }
    let rows = a.len();
    let mut diagonal = a.clone();
    let mut left = identity(rows, c)?;
    let mut right = identity(cols, c)?;
    let mut rank = 0;
    for k in 0..rows.min(cols) {
        let mut pivot: Option<(usize, usize)> = None;
        for i in k..rows {
            for j in k..cols {
                tick(c)?;
                if !diagonal[i][j].is_zero()
                    && pivot.is_none_or(|(p, q)| diagonal[i][j].abs() < diagonal[p][q].abs())
                {
                    pivot = Some((i, j));
                }
            }
        }
        let Some((i, j)) = pivot else { break };
        diagonal.swap(k, i);
        left.swap(k, i);
        for row in &mut diagonal {
            tick(c)?;
            row.swap(k, j);
        }
        for row in &mut right {
            tick(c)?;
            row.swap(k, j);
        }
        loop {
            tick(c)?;
            // Euclid除算。非零剰余をpivotへ移すたび絶対値が減少する。
            if let Some(i) = (k + 1..rows).find(|&i| !diagonal[i][k].is_zero()) {
                let q = -(&diagonal[i][k] / &diagonal[k][k]);
                add_row(&mut diagonal, i, k, &q, c)?;
                add_row(&mut left, i, k, &q, c)?;
                if !diagonal[i][k].is_zero() {
                    diagonal.swap(i, k);
                    left.swap(i, k);
                }
                continue;
            }
            if let Some(j) = (k + 1..cols).find(|&j| !diagonal[k][j].is_zero()) {
                let q = -(&diagonal[k][j] / &diagonal[k][k]);
                add_col(&mut diagonal, j, k, &q, c)?;
                add_col(&mut right, j, k, &q, c)?;
                if !diagonal[k][j].is_zero() {
                    for row in &mut diagonal {
                        tick(c)?;
                        row.swap(j, k);
                    }
                    for row in &mut right {
                        tick(c)?;
                        row.swap(j, k);
                    }
                }
                continue;
            }
            let mut indivisible = None;
            for i in k + 1..rows {
                for j in k + 1..cols {
                    tick(c)?;
                    if (&diagonal[i][j] % &diagonal[k][k]) != Z::zero() {
                        indivisible = Some(i);
                        break;
                    }
                }
                if indivisible.is_some() {
                    break;
                }
            }
            if let Some(i) = indivisible {
                add_row(&mut diagonal, k, i, &Z::one(), c)?;
                add_row(&mut left, k, i, &Z::one(), c)?;
                continue;
            }
            break;
        }
        if diagonal[k][k].is_negative() {
            for v in &mut diagonal[k] {
                tick(c)?;
                *v = -v.clone();
            }
            for v in &mut left[k] {
                tick(c)?;
                *v = -v.clone();
            }
        }
        rank += 1;
    }
    let rhs_column = rhs.iter().map(|x| vec![x.clone()]).collect();
    let transformed_rhs = multiply(&left, &rhs_column, 1, c)?
        .into_iter()
        .map(|r| r[0].clone())
        .collect::<Vec<_>>();
    let mut coordinate = vec![Z::zero(); cols];
    let mut obstruction = None;
    for i in 0..rows {
        tick(c)?;
        if i < rank {
            if (&transformed_rhs[i] % &diagonal[i][i]) != Z::zero() {
                obstruction = Some(i);
                break;
            }
            coordinate[i] = &transformed_rhs[i] / &diagonal[i][i];
        } else if !transformed_rhs[i].is_zero() {
            obstruction = Some(i);
            break;
        }
    }
    let particular = if obstruction.is_none() {
        Some(
            multiply(
                &right,
                &coordinate.into_iter().map(|x| vec![x]).collect(),
                1,
                c,
            )?
            .into_iter()
            .map(|r| r[0].clone())
            .collect(),
        )
    } else {
        None
    };
    let mut kernel = vec![];
    for row in &right {
        tick(c)?;
        kernel.push(row[rank..].to_vec());
    }
    Ok(Fiber {
        diagonal,
        left,
        right,
        transformed_rhs,
        rank,
        particular,
        kernel,
        obstruction,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn control() -> Control {
        Control::unlimited()
    }
    fn matrix(rows: &[&[i64]]) -> Matrix {
        rows.iter()
            .map(|r| r.iter().copied().map(Z::from).collect())
            .collect()
    }
    #[test]
    fn small_signed_matrices_have_unimodular_smith_certificates() {
        let c = control();
        let determinant = |m: &Matrix| &m[0][0] * &m[1][1] - &m[0][1] * &m[1][0];
        for a in -2..=2 {
            for b in -2..=2 {
                for d in -2..=2 {
                    for e in -2..=2 {
                        let original = matrix(&[&[a, b], &[d, e]]);
                        let f = solve(&original, 2, &[Z::one(), Z::zero()], &c).unwrap();
                        assert_eq!(determinant(&f.left).abs(), Z::one());
                        assert_eq!(determinant(&f.right).abs(), Z::one());
                        assert_eq!(
                            multiply(
                                &multiply(&f.left, &original, 2, &c).unwrap(),
                                &f.right,
                                2,
                                &c
                            )
                            .unwrap(),
                            f.diagonal
                        );
                        assert!(f.diagonal[0][1].is_zero() && f.diagonal[1][0].is_zero());
                        if f.rank == 2 {
                            assert!((&f.diagonal[1][1] % &f.diagonal[0][0]).is_zero());
                        }
                    }
                }
            }
        }
    }
    #[test]
    fn integer_elimination_stops_at_every_checkpoint() {
        use std::{cell::Cell, rc::Rc};
        let run = |stop: Option<usize>| {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let c = Control::new(move |_| {
                seen.set(seen.get() + 1);
                stop.filter(|n| *n == seen.get())
                    .map(|_| crate::result::Signal::Term)
            });
            let result = solve(
                &matrix(&[&[6, 4], &[2, 8]]),
                2,
                &[Z::from(10), Z::from(10)],
                &c,
            );
            (result, count.get())
        };
        let (complete, count) = run(None);
        assert!(complete.unwrap().particular.is_some());
        for at in 1..=count {
            assert!(
                matches!(run(Some(at)).0, Err(ValidationFailure::Stop(_))),
                "checkpoint {at}"
            );
        }
    }
    #[test]
    fn exact_integer_fibers_keep_all_directions_and_divisibility_obstructions() {
        let c = control();
        for (a, n, b) in [
            (matrix(&[&[1, 1]]), 2, vec![1]),
            (matrix(&[&[1, 1], &[1, 0]]), 2, vec![1, 0]),
            (matrix(&[&[2, 4]]), 2, vec![1]),
            (matrix(&[&[2, 0], &[0, 3]]), 2, vec![4, 6]),
            (matrix(&[&[2, -4, 6], &[4, -8, 12]]), 3, vec![2, 4]),
            (matrix(&[&[0, 0]]), 2, vec![1]),
            (vec![], 2, vec![]),
            (matrix(&[&[]]), 0, vec![0]),
        ] {
            let rhs = b.into_iter().map(Z::from).collect::<Vec<_>>();
            let f = solve(&a, n, &rhs, &c).unwrap();
            assert_eq!(
                multiply(&multiply(&f.left, &a, n, &c).unwrap(), &f.right, n, &c).unwrap(),
                f.diagonal
            );
            assert!(
                multiply(&a, &f.kernel, n - f.rank, &c)
                    .unwrap()
                    .iter()
                    .flatten()
                    .all(Zero::is_zero)
            );
            if let Some(p) = f.particular {
                assert_eq!(
                    multiply(&a, &p.into_iter().map(|x| vec![x]).collect(), 1, &c).unwrap(),
                    rhs.into_iter().map(|x| vec![x]).collect::<Matrix>()
                );
            } else {
                assert!(f.obstruction.is_some());
            }
        }
        let total = solve(&matrix(&[&[1, 1]]), 2, &[Z::one()], &c).unwrap();
        assert_eq!(total.rank, 1);
        assert!(total.particular.is_some());
        let pinned = solve(&matrix(&[&[1, 1], &[1, 0]]), 2, &[Z::one(), Z::zero()], &c).unwrap();
        assert_eq!(pinned.particular, Some(vec![Z::zero(), Z::one()]));
        assert_eq!(pinned.rank, 2);
        assert!(
            solve(&matrix(&[&[2, 4]]), 2, &[Z::one()], &c)
                .unwrap()
                .particular
                .is_none()
        );
    }
}
