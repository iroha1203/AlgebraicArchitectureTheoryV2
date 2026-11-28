//! 有限次元局所 Artin 環・冪零商環 $A/\mathfrak{m}^{r+1}$・平方零拡大 $R' \twoheadrightarrow R$
//! （$M^2 = 0$ 実検査付き）・体上 RREF 線形代数エンジン（G-141 E1–E5・F2–F8・H2–H6）。

use crate::algebra::poly::AlgebraError;
use crate::algebra::scalar::RingCoeff;
use crate::algebra::syzygy::FieldCoeff;

pub use crate::algebra::artin_quotient::{
    LocalArtinQuotient, SquareZeroExtension, enumerate_monomials_up_to,
};

/// 有限次元局所 Artin 商環の既定安全次元上限。
pub use crate::limits::DEFAULT_MAX_ARTIN_DIM;

/// 体 `K`（`Q`・`F_p`）上のアフィン線形系 `L x = b` の全解または不存在 certificate。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AffineSolutionField<C: FieldCoeff> {
    Consistent {
        particular: Vec<C>,
        kernel_basis: Vec<Vec<C>>,
        verified: bool,
    },
    Inconsistent {
        certificate: Vec<C>,
        verified: bool,
    },
}

/// RREF 分解の結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RrefResult<C: FieldCoeff> {
    pub matrix: Vec<Vec<C>>,
    pub pivot_cols: Vec<usize>,
    pub rank: usize,
}

pub(crate) fn check_same_ring<C: RingCoeff>(expected: &C, actual: &C) -> Result<(), AlgebraError> {
    if !expected.same_ring(actual) {
        return Err(AlgebraError::DomainMismatch {
            expected: format!("{expected:?}"),
            actual: format!("{actual:?}"),
        });
    }
    Ok(())
}

/// 体 `K` 上の行列の簡約行階段形（RREF）を計算する。
pub fn rref_field<C: FieldCoeff>(
    matrix: &[Vec<C>],
    num_cols: usize,
    zero_c: &C,
) -> Result<RrefResult<C>, AlgebraError> {
    let m = matrix.len();
    for row in matrix {
        if row.len() != num_cols {
            return Err(AlgebraError::ArityMismatch {
                expected: num_cols,
                actual: row.len(),
            });
        }
        for val in row {
            check_same_ring(zero_c, val)?;
        }
    }
    let mut a = matrix.to_vec();
    let mut pivot_cols = Vec::new();
    let mut pivot_row = 0usize;
    for col in 0..num_cols {
        if pivot_row >= m {
            break;
        }
        let Some(found) = (pivot_row..m).find(|&r| !a[r][col].coeff_is_zero()) else {
            continue;
        };
        a.swap(pivot_row, found);
        let inv = a[pivot_row][col]
            .coeff_inv()
            .expect("pivot is nonzero in field");
        for val in &mut a[pivot_row][col..num_cols] {
            *val = val.mul_ref(&inv);
        }
        for r in 0..m {
            if r == pivot_row || a[r][col].coeff_is_zero() {
                continue;
            }
            let factor = a[r][col].clone();
            let piv = a[pivot_row][col..num_cols].to_vec();
            for (dst, pv) in a[r][col..num_cols].iter_mut().zip(&piv) {
                let prod = factor.mul_ref(pv);
                *dst = dst.sub_ref(&prod);
            }
            a[r][col] = zero_c.zero_like();
        }
        pivot_cols.push(col);
        pivot_row += 1;
    }
    Ok(RrefResult {
        matrix: a,
        rank: pivot_cols.len(),
        pivot_cols,
    })
}

/// 体 `K`（`Q`・`F_p`）上の線形系 `L x = b` を RREF で解き、独立検算する。
pub fn solve_affine_field<C: FieldCoeff>(
    matrix: &[Vec<C>],
    rhs: &[C],
    num_vars: usize,
    zero_c: &C,
) -> Result<AffineSolutionField<C>, AlgebraError> {
    let m = matrix.len();
    if rhs.len() != m {
        return Err(AlgebraError::ArityMismatch {
            expected: m,
            actual: rhs.len(),
        });
    }
    for row in matrix {
        if row.len() != num_vars {
            return Err(AlgebraError::ArityMismatch {
                expected: num_vars,
                actual: row.len(),
            });
        }
        for val in row {
            check_same_ring(zero_c, val)?;
        }
    }
    for val in rhs {
        check_same_ring(zero_c, val)?;
    }
    let z = zero_c.zero_like();
    let o = zero_c.one_like();
    let mut a = matrix.to_vec();
    let mut b = rhs.to_vec();
    let mut t: Vec<Vec<C>> = (0..m)
        .map(|i| {
            let mut row = vec![z.clone(); m];
            row[i] = o.clone();
            row
        })
        .collect();

    let mut pivot_cols: Vec<(usize, usize)> = Vec::new();
    let mut pivot_row = 0usize;
    for col in 0..num_vars {
        if pivot_row >= m {
            break;
        }
        let Some(found) = (pivot_row..m).find(|&r| !a[r][col].coeff_is_zero()) else {
            continue;
        };
        a.swap(pivot_row, found);
        b.swap(pivot_row, found);
        t.swap(pivot_row, found);

        let inv = a[pivot_row][col].coeff_inv().expect("nonzero pivot");
        for val in &mut a[pivot_row][col..num_vars] {
            *val = val.mul_ref(&inv);
        }
        b[pivot_row] = b[pivot_row].mul_ref(&inv);
        for val in &mut t[pivot_row] {
            *val = val.mul_ref(&inv);
        }

        for r in 0..m {
            if r == pivot_row || a[r][col].coeff_is_zero() {
                continue;
            }
            let factor = a[r][col].clone();
            let piv_a = a[pivot_row][col..num_vars].to_vec();
            for (dst, pv) in a[r][col..num_vars].iter_mut().zip(&piv_a) {
                let prod = factor.mul_ref(pv);
                *dst = dst.sub_ref(&prod);
            }
            let prod_b = factor.mul_ref(&b[pivot_row]);
            b[r] = b[r].sub_ref(&prod_b);
            let piv_t = t[pivot_row].clone();
            for (dst, pv) in t[r].iter_mut().zip(&piv_t) {
                let prod_t = factor.mul_ref(pv);
                *dst = dst.sub_ref(&prod_t);
            }
        }
        pivot_cols.push((pivot_row, col));
        pivot_row += 1;
    }

    for r in pivot_row..m {
        if !b[r].coeff_is_zero() {
            let cert = t[r].clone();
            let verified = verify_inconsistent_field(matrix, rhs, &cert, num_vars, &z);
            return Ok(AffineSolutionField::Inconsistent {
                certificate: cert,
                verified,
            });
        }
    }

    let is_pivot: Vec<bool> = (0..num_vars)
        .map(|c| pivot_cols.iter().any(|&(_, pc)| pc == c))
        .collect();
    let mut particular = vec![z.clone(); num_vars];
    for &(r, col) in &pivot_cols {
        particular[col] = b[r].clone();
    }

    let mut kernel_basis = Vec::new();
    for free_col in 0..num_vars {
        if is_pivot[free_col] {
            continue;
        }
        let mut vec = vec![z.clone(); num_vars];
        vec[free_col] = o.clone();
        for &(r, pcol) in &pivot_cols {
            vec[pcol] = a[r][free_col].neg_ref();
        }
        kernel_basis.push(vec);
    }

    let verified = verify_consistent_field(matrix, rhs, &particular, &kernel_basis, &z);
    Ok(AffineSolutionField::Consistent {
        particular,
        kernel_basis,
        verified,
    })
}

fn verify_consistent_field<C: FieldCoeff>(
    matrix: &[Vec<C>],
    rhs: &[C],
    particular: &[C],
    kernel_basis: &[Vec<C>],
    zero: &C,
) -> bool {
    for (row, target) in matrix.iter().zip(rhs) {
        let mut acc = zero.zero_like();
        for (a, x) in row.iter().zip(particular) {
            acc = acc.add_ref(&a.mul_ref(x));
        }
        if acc != *target {
            return false;
        }
    }
    for v in kernel_basis {
        for row in matrix {
            let mut acc = zero.zero_like();
            for (a, x) in row.iter().zip(v) {
                acc = acc.add_ref(&a.mul_ref(x));
            }
            if !acc.coeff_is_zero() {
                return false;
            }
        }
    }
    true
}

fn verify_inconsistent_field<C: FieldCoeff>(
    matrix: &[Vec<C>],
    rhs: &[C],
    cert: &[C],
    num_vars: usize,
    zero: &C,
) -> bool {
    for col in 0..num_vars {
        let mut acc = zero.zero_like();
        for (r, row) in matrix.iter().enumerate() {
            acc = acc.add_ref(&cert[r].mul_ref(&row[col]));
        }
        if !acc.coeff_is_zero() {
            return false;
        }
    }
    let mut rhs_acc = zero.zero_like();
    for (c, b) in cert.iter().zip(rhs) {
        rhs_acc = rhs_acc.add_ref(&c.mul_ref(b));
    }
    !rhs_acc.coeff_is_zero()
}

/// 有限自由基底を持つ可換結合単位的 `C`-代数（局所 Artin 環・冪零商環の共通表現）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteAlgebra<C: RingCoeff> {
    pub basis_names: Vec<String>,
    pub zero_coeff: C,
    pub one: Vec<C>,
    /// `mul_table[i][j]` は基底元 `e_i * e_j` の座標ベクトル。
    pub mul_table: Vec<Vec<Vec<C>>>,
}

impl<C: RingCoeff> FiniteAlgebra<C> {
    /// 基底環 `C` 自身（1 次元代数）。
    pub fn base_ring(zero_coeff: C) -> Self {
        let z = zero_coeff.zero_like();
        let o = z.one_like();
        Self {
            basis_names: vec!["1".to_owned()],
            zero_coeff: z,
            one: vec![o.clone()],
            mul_table: vec![vec![vec![o]]],
        }
    }

    /// 1 変数打ち切り冪零商環 `C[var]/(var^{max_deg + 1})`（基底 `1, var, ..., var^{max_deg}`）。
    /// `max_deg + 1 > DEFAULT_MAX_ARTIN_DIM`（またはオーバーフロー）時は fail-closed に `OutOfScope` を返す。
    pub fn truncated_univariate(
        var_name: &str,
        max_deg: usize,
        zero_coeff: C,
    ) -> Result<Self, AlgebraError> {
        let Some(dim) = max_deg.checked_add(1) else {
            return Err(AlgebraError::OutOfScope {
                detail: "truncated_univariate max_deg overflow".to_owned(),
            });
        };
        let max_artin_dim = crate::limits::active_limits().max_artin_dim;
        if dim > max_artin_dim {
            return Err(AlgebraError::OutOfScope {
                detail: format!(
                    "truncated_univariate dimension {dim} exceeds limit {max_artin_dim}"
                ),
            });
        }
        let z = zero_coeff.zero_like();
        let o = z.one_like();
        let basis_names: Vec<String> = (0..dim)
            .map(|d| match d {
                0 => "1".to_owned(),
                1 => var_name.to_owned(),
                k => format!("{var_name}^{k}"),
            })
            .collect();
        let mut one = vec![z.clone(); dim];
        one[0] = o.clone();
        let mut mul_table = vec![vec![vec![z.clone(); dim]; dim]; dim];
        for i in 0..dim {
            for j in 0..dim {
                if i + j < dim {
                    mul_table[i][j][i + j] = o.clone();
                }
            }
        }
        Ok(Self {
            basis_names,
            zero_coeff: z,
            one,
            mul_table,
        })
    }

    pub fn dim(&self) -> usize {
        self.basis_names.len()
    }

    pub fn zero_elem(&self) -> Vec<C> {
        vec![self.zero_coeff.zero_like(); self.dim()]
    }

    pub fn one_elem(&self) -> Vec<C> {
        self.one.clone()
    }

    pub fn basis_elem(&self, idx: usize) -> Vec<C> {
        let mut v = self.zero_elem();
        v[idx] = self.zero_coeff.one_like();
        v
    }

    pub fn is_zero_elem(&self, a: &[C]) -> bool {
        a.iter().all(RingCoeff::coeff_is_zero)
    }

    pub fn add(&self, a: &[C], b: &[C]) -> Vec<C> {
        a.iter().zip(b).map(|(x, y)| x.add_ref(y)).collect()
    }

    pub fn sub(&self, a: &[C], b: &[C]) -> Vec<C> {
        a.iter().zip(b).map(|(x, y)| x.sub_ref(y)).collect()
    }

    pub fn neg(&self, a: &[C]) -> Vec<C> {
        a.iter().map(RingCoeff::neg_ref).collect()
    }

    pub fn scale(&self, a: &[C], s: &C) -> Vec<C> {
        a.iter().map(|x| x.mul_ref(s)).collect()
    }

    pub fn mul(&self, a: &[C], b: &[C]) -> Vec<C> {
        let d = self.dim();
        let mut out = self.zero_elem();
        for (i, ai) in a.iter().enumerate() {
            if ai.coeff_is_zero() {
                continue;
            }
            for (j, bj) in b.iter().enumerate() {
                if bj.coeff_is_zero() {
                    continue;
                }
                let coeff = ai.mul_ref(bj);
                for (k, entry) in self.mul_table[i][j].iter().enumerate().take(d) {
                    if !entry.coeff_is_zero() {
                        let term = coeff.mul_ref(entry);
                        out[k] = out[k].add_ref(&term);
                    }
                }
            }
        }
        out
    }

    pub fn pow(&self, base: &[C], mut exp: u32) -> Vec<C> {
        if exp == 0 {
            return self.one_elem();
        }
        let mut acc = self.one_elem();
        let mut b = base.to_vec();
        while exp > 0 {
            if exp & 1 == 1 {
                acc = self.mul(&acc, &b);
            }
            exp >>= 1;
            if exp > 0 {
                b = self.mul(&b, &b);
            }
        }
        acc
    }

    /// 係数環の多項式 `poly` を本代数上の元タプル `values` で評価する。
    pub fn eval_poly(
        &self,
        poly: &crate::algebra::poly::Poly<C>,
        values: &[Vec<C>],
    ) -> Result<Vec<C>, AlgebraError> {
        if poly.num_vars() != values.len() {
            return Err(AlgebraError::ArityMismatch {
                expected: poly.num_vars(),
                actual: values.len(),
            });
        }
        check_same_ring(&self.zero_coeff, poly.zero_coeff())?;
        for v in values {
            if v.len() != self.dim() {
                return Err(AlgebraError::ArityMismatch {
                    expected: self.dim(),
                    actual: v.len(),
                });
            }
            for c in v {
                check_same_ring(&self.zero_coeff, c)?;
            }
        }
        let mut acc = self.zero_elem();
        for (mono, coeff) in poly.terms() {
            let mut term = self.scale(&self.one, coeff);
            for (idx, &e) in mono.exps().iter().enumerate() {
                if e > 0 {
                    let p = self.pow(&values[idx], e);
                    term = self.mul(&term, &p);
                }
            }
            acc = self.add(&acc, &term);
        }
        Ok(acc)
    }

    /// 可換・結合・単位元の公理を乗法表全体で検証する。
    pub fn verify_ring_axioms(&self) -> Result<(), AlgebraError> {
        let d = self.dim();
        if d == 0 || self.one.len() != d || self.mul_table.len() != d {
            return Err(AlgebraError::OutOfScope {
                detail: "finite algebra dimension or identity vector is malformed".to_owned(),
            });
        }
        for c in &self.one {
            check_same_ring(&self.zero_coeff, c)?;
        }
        for row in &self.mul_table {
            if row.len() != d || row.iter().any(|v| v.len() != d) {
                return Err(AlgebraError::OutOfScope {
                    detail: "finite algebra multiplication table shape mismatch".to_owned(),
                });
            }
            for vec in row {
                for c in vec {
                    check_same_ring(&self.zero_coeff, c)?;
                }
            }
        }
        for i in 0..d {
            let ei = self.basis_elem(i);
            if self.mul(&self.one, &ei) != ei || self.mul(&ei, &self.one) != ei {
                return Err(AlgebraError::OutOfScope {
                    detail: "finite algebra identity axiom violated".to_owned(),
                });
            }
            for j in i..d {
                if self.mul_table[i][j] != self.mul_table[j][i] {
                    return Err(AlgebraError::OutOfScope {
                        detail: "finite algebra commutativity violated".to_owned(),
                    });
                }
            }
        }
        for i in 0..d {
            let ei = self.basis_elem(i);
            for j in 0..d {
                let ij = &self.mul_table[i][j];
                for k in 0..d {
                    let ek = self.basis_elem(k);
                    let lhs = self.mul(ij, &ek);
                    let rhs = self.mul(&ei, &self.mul_table[j][k]);
                    if lhs != rhs {
                        return Err(AlgebraError::OutOfScope {
                            detail: "finite algebra associativity violated".to_owned(),
                        });
                    }
                }
            }
        }
        Ok(())
    }

    pub fn format_elem(&self, elem: &[C]) -> String {
        let mut out = String::new();
        for (idx, c) in elem.iter().enumerate() {
            if c.coeff_is_zero() {
                continue;
            }
            let s = c.to_string();
            let neg = s.starts_with('-');
            let abs = s.strip_prefix('-').unwrap_or(&s);
            if out.is_empty() {
                if neg {
                    out.push('-');
                }
            } else if neg {
                out.push_str(" - ");
            } else {
                out.push_str(" + ");
            }
            let bname = &self.basis_names[idx];
            if bname == "1" {
                out.push_str(abs);
            } else if abs == "1" {
                out.push_str(bname);
            } else {
                out.push_str(abs);
                out.push('*');
                out.push_str(bname);
            }
        }
        if out.is_empty() { "0".to_owned() } else { out }
    }
}
