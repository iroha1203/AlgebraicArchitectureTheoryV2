//! 作用素と右辺を分離した Smith 標準形（$\mathbb{Z}$ / $\mathbb{Q}$）の分解保持と再評価検算
//! （AAT 第19章 補題 19.6・定理 19.7）。

use crate::algebra::artin::solve_affine_field;
use crate::algebra::cochain::{mat_mul, mat_vec};
use crate::algebra::linear::smith_normal_form_z;
use crate::algebra::poly::AlgebraError;
use crate::algebra::scalar::{Rat, RingCoeff};
use crate::algebra::syzygy::FieldCoeff;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

/// $\mathbb{Z}$ 上の再利用可能な Smith 標準形 $U M V = D = \operatorname{diag}(d_1, \dots, d_r, 0, \dots, 0)$。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnfFactorizationZ {
    pub rows: usize,
    pub cols: usize,
    pub u: Vec<Vec<BigInt>>,
    pub v: Vec<Vec<BigInt>>,
    pub diagonals: Vec<BigInt>,
    pub rank: usize,
    pub kernel_basis: Vec<Vec<BigInt>>,
    pub cokernel_torsion: Vec<BigInt>,
    pub cokernel_free_rank: usize,
    pub umv_verified: bool,
    pub unimodular_verified: bool,
    pub divisibility_verified: bool,
}

/// $\mathbb{Z}$ 上で新しい右辺 $b$ を SNF へ通した復元結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnfRhsSolutionZ {
    pub solvable: bool,
    pub transformed_rhs: Vec<BigInt>,
    pub particular: Option<Vec<BigInt>>,
    pub kernel_basis: Vec<Vec<BigInt>>,
    pub failing_row_index: Option<usize>,
    pub divisor: Option<BigInt>,
    pub rhs_value: Option<BigInt>,
    pub reeval_verified: bool,
}

impl SnfFactorizationZ {
    /// 整数行列 `matrix` ($m \times n$) の SNF を計算し、$UMV = D$・$|\det U| = |\det V| = 1$・整除鎖を検算する。
    pub fn compute(matrix: &[Vec<BigInt>], num_cols: usize) -> Result<Self, AlgebraError> {
        let rows = matrix.len();
        let snf = smith_normal_form_z(matrix, num_cols)?;
        let rank = snf.rank;

        let mut d_expected = vec![vec![BigInt::zero(); num_cols]; rows];
        for (i, diag) in snf.diagonals.iter().enumerate() {
            d_expected[i][i] = diag.clone();
        }
        let um = mat_mul(&snf.u, matrix, num_cols, &BigInt::zero());
        let umv = mat_mul(&um, &snf.v, num_cols, &BigInt::zero());
        let umv_verified = umv == d_expected;

        let det_u = determinant_z(&snf.u)?;
        let det_v = determinant_z(&snf.v)?;
        let unimodular_verified = det_u.abs().is_one() && det_v.abs().is_one();

        let divisibility_verified = snf.diagonals.iter().all(|d| d > &BigInt::zero())
            && snf.diagonals.windows(2).all(|w| (&w[1] % &w[0]).is_zero());

        let mut kernel_basis = Vec::new();
        for free_col in rank..num_cols {
            let col_vec: Vec<BigInt> = snf.v.iter().map(|r| r[free_col].clone()).collect();
            kernel_basis.push(col_vec);
        }

        let cokernel_torsion: Vec<BigInt> = snf
            .diagonals
            .iter()
            .filter(|d| *d > &BigInt::one())
            .cloned()
            .collect();
        let cokernel_free_rank = rows - rank;

        Ok(Self {
            rows,
            cols: num_cols,
            u: snf.u,
            v: snf.v,
            diagonals: snf.diagonals,
            rank,
            kernel_basis,
            cokernel_torsion,
            cokernel_free_rank,
            umv_verified,
            unimodular_verified,
            divisibility_verified,
        })
    }

    /// 既存分解を再利用して右辺 `rhs` に対する全解 $Mp = b$ を復元し、元行列で再評価検算する。
    pub fn solve_rhs(
        &self,
        original_m: &[Vec<BigInt>],
        rhs: &[BigInt],
    ) -> Result<SnfRhsSolutionZ, AlgebraError> {
        if original_m.len() != self.rows || rhs.len() != self.rows {
            return Err(AlgebraError::ArityMismatch {
                expected: self.rows,
                actual: rhs.len(),
            });
        }
        let u_rhs = mat_vec(&self.u, rhs, &BigInt::zero());

        for (i, diag) in self.diagonals.iter().enumerate() {
            if !(&u_rhs[i] % diag).is_zero() {
                let cert = &self.u[i];
                let lhs_row = left_mul_row_z(cert, original_m, self.cols);
                let rhs_dot = dot_z(cert, rhs);
                let reeval_verified =
                    lhs_row.iter().all(|v| (v % diag).is_zero()) && !(rhs_dot % diag).is_zero();
                return Ok(SnfRhsSolutionZ {
                    solvable: false,
                    transformed_rhs: u_rhs.clone(),
                    particular: None,
                    kernel_basis: self.kernel_basis.clone(),
                    failing_row_index: Some(i),
                    divisor: Some(diag.clone()),
                    rhs_value: Some(u_rhs[i].clone()),
                    reeval_verified,
                });
            }
        }
        for (j, val) in u_rhs.iter().enumerate().skip(self.rank) {
            if !val.is_zero() {
                let cert = &self.u[j];
                let lhs_row = left_mul_row_z(cert, original_m, self.cols);
                let rhs_dot = dot_z(cert, rhs);
                let reeval_verified = lhs_row.iter().all(BigInt::is_zero) && !rhs_dot.is_zero();
                return Ok(SnfRhsSolutionZ {
                    solvable: false,
                    transformed_rhs: u_rhs.clone(),
                    particular: None,
                    kernel_basis: self.kernel_basis.clone(),
                    failing_row_index: Some(j),
                    divisor: None,
                    rhs_value: Some(val.clone()),
                    reeval_verified,
                });
            }
        }

        let mut y0 = vec![BigInt::zero(); self.cols];
        for (i, diag) in self.diagonals.iter().enumerate() {
            y0[i] = &u_rhs[i] / diag;
        }
        let particular = mat_vec(&self.v, &y0, &BigInt::zero());

        let mp = mat_vec(original_m, &particular, &BigInt::zero());
        let particular_ok = mp == rhs;
        let kernel_ok = self.kernel_basis.iter().all(|k| {
            mat_vec(original_m, k, &BigInt::zero())
                .iter()
                .all(BigInt::is_zero)
        });

        Ok(SnfRhsSolutionZ {
            solvable: true,
            transformed_rhs: u_rhs,
            particular: Some(particular),
            kernel_basis: self.kernel_basis.clone(),
            failing_row_index: None,
            divisor: None,
            rhs_value: None,
            reeval_verified: particular_ok && kernel_ok,
        })
    }
}

/// $\mathbb{Q}$ 上の再利用可能な標準形 $U M V = \operatorname{diag}(1, \dots, 1, 0, \dots, 0)$。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnfFactorizationQ {
    pub rows: usize,
    pub cols: usize,
    pub u: Vec<Vec<Rat>>,
    pub v: Vec<Vec<Rat>>,
    pub rank: usize,
    pub kernel_basis: Vec<Vec<Rat>>,
    pub cokernel_rank: usize,
    pub umv_verified: bool,
    pub invertible_verified: bool,
}

/// $\mathbb{Q}$ 上で新しい右辺 $b$ を SNF へ通した復元結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnfRhsSolutionQ {
    pub solvable: bool,
    pub transformed_rhs: Vec<Rat>,
    pub particular: Option<Vec<Rat>>,
    pub kernel_basis: Vec<Vec<Rat>>,
    pub failing_row_index: Option<usize>,
    pub reeval_verified: bool,
}

impl SnfFactorizationQ {
    /// 有理行列 `matrix` ($m \times n$) の分解 $U M V = \operatorname{diag}(1,\dots,1,0,\dots,0)$ を計算・検算する。
    pub fn compute(matrix: &[Vec<Rat>], num_cols: usize) -> Result<Self, AlgebraError> {
        let rows = matrix.len();
        for row in matrix {
            if row.len() != num_cols {
                return Err(AlgebraError::ArityMismatch {
                    expected: num_cols,
                    actual: row.len(),
                });
            }
        }
        let mut d = matrix.to_vec();
        let mut u = identity_q(rows);
        let mut v = identity_q(num_cols);

        let mut k = 0usize;
        while k < rows && k < num_cols {
            let mut pivot = None;
            'search: for (r, row) in d.iter().enumerate().take(rows).skip(k) {
                for (c, val) in row.iter().enumerate().take(num_cols).skip(k) {
                    if !val.coeff_is_zero() {
                        pivot = Some((r, c));
                        break 'search;
                    }
                }
            }
            let Some((pr, pc)) = pivot else {
                break;
            };
            if pr != k {
                d.swap(k, pr);
                u.swap(k, pr);
            }
            if pc != k {
                for row in &mut d {
                    row.swap(k, pc);
                }
                for row in &mut v {
                    row.swap(k, pc);
                }
            }
            let scale = d[k][k].coeff_inv().expect("nonzero pivot");
            for val in &mut d[k] {
                *val = val.mul_ref(&scale);
            }
            for val in &mut u[k] {
                *val = val.mul_ref(&scale);
            }
            for r in 0..rows {
                if r == k || d[r][k].coeff_is_zero() {
                    continue;
                }
                let factor = d[r][k].clone();
                let d_piv = d[k].clone();
                for (dst, pv) in d[r].iter_mut().zip(&d_piv) {
                    *dst = dst.sub_ref(&factor.mul_ref(pv));
                }
                let u_piv = u[k].clone();
                for (dst, pv) in u[r].iter_mut().zip(&u_piv) {
                    *dst = dst.sub_ref(&factor.mul_ref(pv));
                }
            }
            for c in 0..num_cols {
                if c == k || d[k][c].coeff_is_zero() {
                    continue;
                }
                let factor = d[k][c].clone();
                for row in &mut d {
                    let sub = factor.mul_ref(&row[k]);
                    row[c] = row[c].sub_ref(&sub);
                }
                for row in &mut v {
                    let sub = factor.mul_ref(&row[k]);
                    row[c] = row[c].sub_ref(&sub);
                }
            }
            k += 1;
        }

        let mut d_expected = vec![vec![Rat::zero(); num_cols]; rows];
        for (i, row) in d_expected.iter_mut().enumerate().take(k) {
            row[i] = Rat::one();
        }
        let um = mat_mul(&u, matrix, num_cols, &Rat::zero());
        let umv = mat_mul(&um, &v, num_cols, &Rat::zero());
        let umv_verified = umv == d_expected;
        let invertible_verified = is_invertible_q(&u)? && is_invertible_q(&v)?;

        let mut kernel_basis = Vec::new();
        for free_col in k..num_cols {
            let col_vec: Vec<Rat> = v.iter().map(|r| r[free_col].clone()).collect();
            kernel_basis.push(col_vec);
        }

        Ok(Self {
            rows,
            cols: num_cols,
            u,
            v,
            rank: k,
            kernel_basis,
            cokernel_rank: rows - k,
            umv_verified,
            invertible_verified,
        })
    }

    /// 既存分解を再利用して右辺 `rhs` に対する全解 $Mp = b$ を復元し、元行列で再評価検算する。
    pub fn solve_rhs(
        &self,
        original_m: &[Vec<Rat>],
        rhs: &[Rat],
    ) -> Result<SnfRhsSolutionQ, AlgebraError> {
        if original_m.len() != self.rows || rhs.len() != self.rows {
            return Err(AlgebraError::ArityMismatch {
                expected: self.rows,
                actual: rhs.len(),
            });
        }
        let u_rhs = mat_vec(&self.u, rhs, &Rat::zero());
        for (j, val) in u_rhs.iter().enumerate().skip(self.rank) {
            if !val.coeff_is_zero() {
                let cert = &self.u[j];
                let mut lhs_row = vec![Rat::zero(); self.cols];
                for (r_idx, row) in original_m.iter().enumerate() {
                    for (c, v) in row.iter().enumerate() {
                        lhs_row[c] = lhs_row[c].add_ref(&cert[r_idx].mul_ref(v));
                    }
                }
                let mut rhs_dot = Rat::zero();
                for (c, b) in cert.iter().zip(rhs) {
                    rhs_dot = rhs_dot.add_ref(&c.mul_ref(b));
                }
                let reeval_verified =
                    lhs_row.iter().all(RingCoeff::coeff_is_zero) && !rhs_dot.coeff_is_zero();
                return Ok(SnfRhsSolutionQ {
                    solvable: false,
                    transformed_rhs: u_rhs,
                    particular: None,
                    kernel_basis: self.kernel_basis.clone(),
                    failing_row_index: Some(j),
                    reeval_verified,
                });
            }
        }

        let mut y0 = vec![Rat::zero(); self.cols];
        for (i, val) in u_rhs.iter().enumerate().take(self.rank) {
            y0[i] = val.clone();
        }
        let particular = mat_vec(&self.v, &y0, &Rat::zero());
        let mp = mat_vec(original_m, &particular, &Rat::zero());
        let particular_ok = mp == rhs;
        let kernel_ok = self.kernel_basis.iter().all(|k| {
            mat_vec(original_m, k, &Rat::zero())
                .iter()
                .all(RingCoeff::coeff_is_zero)
        });

        Ok(SnfRhsSolutionQ {
            solvable: true,
            transformed_rhs: u_rhs,
            particular: Some(particular),
            kernel_basis: self.kernel_basis.clone(),
            failing_row_index: None,
            reeval_verified: particular_ok && kernel_ok,
        })
    }
}

fn identity_q(n: usize) -> Vec<Vec<Rat>> {
    (0..n)
        .map(|i| {
            let mut row = vec![Rat::zero(); n];
            row[i] = Rat::one();
            row
        })
        .collect()
}

fn is_invertible_q(mat: &[Vec<Rat>]) -> Result<bool, AlgebraError> {
    let n = mat.len();
    if n == 0 {
        return Ok(true);
    }
    let rhs = vec![Rat::zero(); n];
    match solve_affine_field(mat, &rhs, n, &Rat::zero())? {
        crate::algebra::artin::AffineSolutionField::Consistent { kernel_basis, .. } => {
            Ok(kernel_basis.is_empty())
        }
        crate::algebra::artin::AffineSolutionField::Inconsistent { .. } => Ok(false),
    }
}

/// Bareiss 厳密整数行列式（正方行列のみ）。
fn determinant_z(mat: &[Vec<BigInt>]) -> Result<BigInt, AlgebraError> {
    let n = mat.len();
    if n == 0 {
        return Ok(BigInt::one());
    }
    let mut a = mat.to_vec();
    let mut sign = BigInt::one();
    let mut prev = BigInt::one();
    for k in 0..(n - 1) {
        if a[k][k].is_zero() {
            let Some(swap_row) = ((k + 1)..n).find(|&r| !a[r][k].is_zero()) else {
                return Ok(BigInt::zero());
            };
            a.swap(k, swap_row);
            sign = -sign;
        }
        for i in (k + 1)..n {
            for j in (k + 1)..n {
                let num = &a[i][j] * &a[k][k] - &a[i][k] * &a[k][j];
                a[i][j] = num / &prev;
            }
        }
        prev = a[k][k].clone();
    }
    Ok(sign * &a[n - 1][n - 1])
}

fn left_mul_row_z(row_vec: &[BigInt], mat: &[Vec<BigInt>], cols: usize) -> Vec<BigInt> {
    let mut out = vec![BigInt::zero(); cols];
    for (r, m_row) in row_vec.iter().zip(mat) {
        for (c, val) in m_row.iter().enumerate() {
            out[c] += r * val;
        }
    }
    out
}

fn dot_z(a: &[BigInt], b: &[BigInt]) -> BigInt {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}
