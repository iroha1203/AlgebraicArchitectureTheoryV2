//! 平方零拡大 $R' \twoheadrightarrow R$（$M^2 = 0$ 実検査付き）および
//! 局所 Artin 商環 $A/\mathfrak{m}^{r+1}$ の構成（G-141 E1–E5・F2–F4）。

use crate::algebra::artin::{
    AffineSolutionField, FiniteAlgebra, rref_field, solve_affine_field,
};
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Monomial, Poly, VarOrder};
use crate::algebra::scalar::RingCoeff;
use crate::algebra::syzygy::FieldCoeff;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::BTreeMap;

/// 平方零拡大 `R' ↠ R`（kernel `M = ker(π)`、`M² = 0` を実検査済み）（G-141 E1–E5）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SquareZeroExtension<C: RingCoeff> {
    pub r_prime: FiniteAlgebra<C>,
    pub r_base: FiniteAlgebra<C>,
    /// 射影 `π: R' -> R`（`dim(R) x dim(R')` 行列）。
    pub projection: Vec<Vec<C>>,
    /// `M = ker(π)` の `R'` 内基底（各要素は長さ `dim(R')`）。
    pub kernel_basis: Vec<Vec<C>>,
    /// 基底環上での `M² = 0` 検証済みフラグ。
    pub square_zero_verified: bool,
}

impl<C: RingCoeff> SquareZeroExtension<C> {
    pub fn kernel_dim(&self) -> usize {
        self.kernel_basis.len()
    }

    pub fn project(&self, elem_r_prime: &[C]) -> Vec<C> {
        let dr = self.r_base.dim();
        let mut out = vec![self.r_base.zero_coeff.zero_like(); dr];
        for (r_idx, row) in self.projection.iter().enumerate() {
            let mut acc = self.r_base.zero_coeff.zero_like();
            for (p, x) in row.iter().zip(elem_r_prime) {
                acc = acc.add_ref(&p.mul_ref(x));
            }
            out[r_idx] = acc;
        }
        out
    }

    pub fn embed_kernel(&self, m_coords: &[C]) -> Result<Vec<C>, AlgebraError> {
        if m_coords.len() != self.kernel_basis.len() {
            return Err(AlgebraError::ArityMismatch {
                expected: self.kernel_basis.len(),
                actual: m_coords.len(),
            });
        }
        let mut out = self.r_prime.zero_elem();
        for (c, kb) in m_coords.iter().zip(&self.kernel_basis) {
            if !c.coeff_is_zero() {
                let scaled = self.r_prime.scale(kb, c);
                out = self.r_prime.add(&out, &scaled);
            }
        }
        Ok(out)
    }

    /// 環準同型性と `M² = 0` を共通検証する。
    fn verify_common(&self) -> Result<(), AlgebraError> {
        self.r_prime.verify_ring_axioms()?;
        self.r_base.verify_ring_axioms()?;
        let dp = self.r_prime.dim();
        let dr = self.r_base.dim();
        if self.projection.len() != dr || self.projection.iter().any(|row| row.len() != dp) {
            return Err(AlgebraError::OutOfScope {
                detail: "square-zero extension projection matrix dimension mismatch".to_owned(),
            });
        }
        if self.project(&self.r_prime.one) != self.r_base.one {
            return Err(AlgebraError::OutOfScope {
                detail: "projection does not preserve multiplicative identity".to_owned(),
            });
        }
        for i in 0..dp {
            let pi = self.project(&self.r_prime.basis_elem(i));
            for j in i..dp {
                let pj = self.project(&self.r_prime.basis_elem(j));
                let lhs = self.project(&self.r_prime.mul_table[i][j]);
                let rhs = self.r_base.mul(&pi, &pj);
                if lhs != rhs {
                    return Err(AlgebraError::OutOfScope {
                        detail: "projection is not a ring homomorphism".to_owned(),
                    });
                }
            }
        }
        for kb in &self.kernel_basis {
            if kb.len() != dp {
                return Err(AlgebraError::ArityMismatch {
                    expected: dp,
                    actual: kb.len(),
                });
            }
            if !self.r_base.is_zero_elem(&self.project(kb)) {
                return Err(AlgebraError::OutOfScope {
                    detail: "kernel basis element is not mapped to zero by projection".to_owned(),
                });
            }
        }
        for a in &self.kernel_basis {
            for b in &self.kernel_basis {
                let prod = self.r_prime.mul(a, b);
                if !self.r_prime.is_zero_elem(&prod) {
                    return Err(AlgebraError::OutOfScope {
                        detail: "square-zero condition M^2 = 0 violated in extension R' ->> R"
                            .to_owned(),
                    });
                }
            }
        }
        Ok(())
    }
}

impl<C: FieldCoeff> SquareZeroExtension<C> {
    /// 体係数上の平方零拡大 `R' ↠ R` を構築し、全射性・環準同型性・`M = ker π`・`M² = 0` を検証する。
    pub fn new_field(
        r_prime: FiniteAlgebra<C>,
        r_base: FiniteAlgebra<C>,
        projection: Vec<Vec<C>>,
    ) -> Result<Self, AlgebraError> {
        let dp = r_prime.dim();
        let dr = r_base.dim();
        let z = r_prime.zero_coeff.zero_like();
        let rref = rref_field(&projection, dp, &z)?;
        if rref.rank != dr {
            return Err(AlgebraError::OutOfScope {
                detail: "square-zero extension projection R' -> R is not surjective".to_owned(),
            });
        }
        let zero_rhs = vec![z.clone(); dr];
        let AffineSolutionField::Consistent { kernel_basis, .. } =
            solve_affine_field(&projection, &zero_rhs, dp, &z)?
        else {
            return Err(AlgebraError::OutOfScope {
                detail: "failed to compute kernel basis of projection".to_owned(),
            });
        };
        let ext = Self {
            r_prime,
            r_base,
            projection,
            kernel_basis,
            square_zero_verified: true,
        };
        ext.verify_common()?;
        Ok(ext)
    }

    /// 1 変数冪零商の 1 段拡大 `K[var]/(var^{deg_r + 2}) ↠ K[var]/(var^{deg_r + 1})`（`deg_r >= 0`）。
    pub fn truncated_step_field(
        var_name: &str,
        deg_r: usize,
        zero_coeff: C,
    ) -> Result<Self, AlgebraError> {
        let r_base = FiniteAlgebra::truncated_univariate(var_name, deg_r, zero_coeff.clone());
        let r_prime = FiniteAlgebra::truncated_univariate(var_name, deg_r + 1, zero_coeff.clone());
        let dr = r_base.dim();
        let dp = r_prime.dim();
        let z = zero_coeff.zero_like();
        let o = z.one_like();
        let mut projection = vec![vec![z; dp]; dr];
        for (i, row) in projection.iter_mut().enumerate().take(dr) {
            row[i] = o.clone();
        }
        Self::new_field(r_prime, r_base, projection)
    }

    /// `R'` の元 `elem` が `M = ker π` に属することを検査し、`kernel_basis` の座標へ展開する。
    pub fn extract_kernel_coords_field(&self, elem: &[C]) -> Result<Vec<C>, AlgebraError> {
        if !self.r_base.is_zero_elem(&self.project(elem)) {
            return Err(AlgebraError::OutOfScope {
                detail: "element does not lie in kernel M = ker(R' -> R)".to_owned(),
            });
        }
        let m_dim = self.kernel_basis.len();
        let dp = self.r_prime.dim();
        let z = self.r_prime.zero_coeff.zero_like();
        let mut mat = vec![vec![z.clone(); m_dim]; dp];
        for (col, kb) in self.kernel_basis.iter().enumerate() {
            for (row, val) in kb.iter().enumerate() {
                mat[row][col] = val.clone();
            }
        }
        match solve_affine_field(&mat, elem, m_dim, &z)? {
            AffineSolutionField::Consistent { particular, .. } => Ok(particular),
            AffineSolutionField::Inconsistent { .. } => Err(AlgebraError::OutOfScope {
                detail: "kernel element could not be expressed in kernel basis".to_owned(),
            }),
        }
    }
}

impl SquareZeroExtension<BigInt> {
    /// 整数係数上の平方零拡大 `R' ↠ R` を構築し、Smith 標準形で全射性と `M = ker π`・`M² = 0` を検証する。
    pub fn new_z(
        r_prime: FiniteAlgebra<BigInt>,
        r_base: FiniteAlgebra<BigInt>,
        projection: Vec<Vec<BigInt>>,
    ) -> Result<Self, AlgebraError> {
        let dp = r_prime.dim();
        let dr = r_base.dim();
        let zero_rhs = vec![BigInt::zero(); dr];
        let AffineSolutionZ::Consistent {
            kernel_basis,
            smith_diagonals,
            ..
        } = solve_affine_z(&projection, &zero_rhs, dp)?
        else {
            return Err(AlgebraError::OutOfScope {
                detail: "failed to compute Z kernel of projection".to_owned(),
            });
        };
        if smith_diagonals.len() != dr || !smith_diagonals.iter().all(One::is_one) {
            return Err(AlgebraError::OutOfScope {
                detail: "Z square-zero extension projection is not surjective over Z".to_owned(),
            });
        }
        let ext = Self {
            r_prime,
            r_base,
            projection,
            kernel_basis,
            square_zero_verified: true,
        };
        ext.verify_common()?;
        Ok(ext)
    }

    /// 整数係数 1 変数冪零商の 1 段拡大 `Z[var]/(var^{deg_r + 2}) ↠ Z[var]/(var^{deg_r + 1})`。
    pub fn truncated_step_z(var_name: &str, deg_r: usize) -> Result<Self, AlgebraError> {
        let r_base = FiniteAlgebra::truncated_univariate(var_name, deg_r, BigInt::zero());
        let r_prime = FiniteAlgebra::truncated_univariate(var_name, deg_r + 1, BigInt::zero());
        let dr = r_base.dim();
        let dp = r_prime.dim();
        let mut projection = vec![vec![BigInt::zero(); dp]; dr];
        for (i, row) in projection.iter_mut().enumerate().take(dr) {
            row[i] = BigInt::one();
        }
        Self::new_z(r_prime, r_base, projection)
    }

    /// `R'` の元が `M = ker π` に属することを検査し、`kernel_basis` 上の整数座標を返す。
    pub fn extract_kernel_coords_z(&self, elem: &[BigInt]) -> Result<Vec<BigInt>, AlgebraError> {
        if !self.r_base.is_zero_elem(&self.project(elem)) {
            return Err(AlgebraError::OutOfScope {
                detail: "element does not lie in Z kernel M = ker(R' -> R)".to_owned(),
            });
        }
        let m_dim = self.kernel_basis.len();
        let dp = self.r_prime.dim();
        let mut mat = vec![vec![BigInt::zero(); m_dim]; dp];
        for (col, kb) in self.kernel_basis.iter().enumerate() {
            for (row, val) in kb.iter().enumerate() {
                mat[row][col] = val.clone();
            }
        }
        match solve_affine_z(&mat, elem, m_dim)? {
            AffineSolutionZ::Consistent { particular, .. } => Ok(particular),
            AffineSolutionZ::Inconsistent { .. } => Err(AlgebraError::OutOfScope {
                detail: "Z kernel element could not be expressed in Z kernel basis".to_owned(),
            }),
        }
    }
}

/// 局所環 `A = (K[z_1, ..., z_d] / I_O)_m` の普遍 Artin 商 `A / m^{r+1}`（G-141 F2–F4）。
#[derive(Clone, Debug)]
pub struct LocalArtinQuotient<C: FieldCoeff> {
    pub vars: VarOrder,
    pub base_point: Vec<C>,
    pub max_deg: usize,
    /// `V_r = K[w]/(w)^{r+1}` の全単項式一覧。
    pub ambient_monomials: Vec<Monomial>,
    /// `A / m^{r+1}` の基底として選ばれた `ambient_monomials` の添字。
    pub free_indices: Vec<usize>,
    /// `V_r -> A / m^{r+1}` の射影行列（`dim(A/m^{r+1}) x dim(V_r)`）。
    pub ambient_to_quotient: Vec<Vec<C>>,
    /// 構成された有限次元局所 Artin 代数 `A / m^{r+1}`。
    pub algebra: FiniteAlgebra<C>,
}

impl<C: FieldCoeff> LocalArtinQuotient<C> {
    /// 任意の有限表示観測環 `K[z]/I_O` と基点 `a` から普遍 Artin 商 `A / m^{r+1}` を構築する。
    pub fn build(
        vars: VarOrder,
        ideal_gens: &[Poly<C>],
        base_point: &[C],
        max_deg: usize,
        zero_coeff: C,
        max_dim: usize,
    ) -> Result<Self, AlgebraError> {
        let d = vars.len();
        if base_point.len() != d {
            return Err(AlgebraError::ArityMismatch {
                expected: d,
                actual: base_point.len(),
            });
        }
        for g in ideal_gens {
            if g.num_vars() != d {
                return Err(AlgebraError::ArityMismatch {
                    expected: d,
                    actual: g.num_vars(),
                });
            }
            let val = g.eval_at(base_point)?;
            if !val.coeff_is_zero() {
                return Err(AlgebraError::OutOfScope {
                    detail: "base point does not satisfy observation presentation ideal I_O"
                        .to_owned(),
                });
            }
        }
        let ambient_monomials = enumerate_monomials_up_to(d, max_deg, max_dim)?;
        let v_dim = ambient_monomials.len();
        let mono_index: BTreeMap<Monomial, usize> = ambient_monomials
            .iter()
            .enumerate()
            .map(|(i, m)| (m.clone(), i))
            .collect();

        let shift_polys = make_shift_polys(d, base_point, &zero_coeff);
        let z = zero_coeff.zero_like();
        let o = z.one_like();

        let mut rel_rows: Vec<Vec<C>> = Vec::new();
        for g in ideal_gens {
            if g.is_zero() {
                continue;
            }
            let shifted = g.substitute(&shift_polys)?.truncate_degree(max_deg as u64);
            if shifted.is_zero() {
                continue;
            }
            for m in &ambient_monomials {
                let m_deg = m.total_degree();
                let mut row = vec![z.clone(); v_dim];
                let mut any = false;
                for (gm, gc) in shifted.terms() {
                    if m_deg + gm.total_degree() <= max_deg as u64 {
                        let prod_m = m.mul(gm);
                        if let Some(&col) = mono_index.get(&prod_m) {
                            row[col] = row[col].add_ref(gc);
                            any = true;
                        }
                    }
                }
                if any {
                    rel_rows.push(row);
                }
            }
        }

        let rref = rref_field(&rel_rows, v_dim, &z)?;
        let pivot_set: BTreeMap<usize, usize> = rref
            .pivot_cols
            .iter()
            .enumerate()
            .map(|(row_idx, &col)| (col, row_idx))
            .collect();
        let free_indices: Vec<usize> = (0..v_dim)
            .filter(|col| !pivot_set.contains_key(col))
            .collect();
        let q_dim = free_indices.len();
        let free_pos: BTreeMap<usize, usize> = free_indices
            .iter()
            .enumerate()
            .map(|(pos, &col)| (col, pos))
            .collect();

        let mut ambient_to_quotient = vec![vec![z.clone(); v_dim]; q_dim];
        for (col, _) in (0..v_dim).enumerate() {
            if let Some(&pos) = free_pos.get(&col) {
                ambient_to_quotient[pos][col] = o.clone();
            } else if let Some(&row_idx) = pivot_set.get(&col) {
                for (&f_col, &pos) in &free_pos {
                    let c = &rref.matrix[row_idx][f_col];
                    if !c.coeff_is_zero() {
                        ambient_to_quotient[pos][col] = c.neg_ref();
                    }
                }
            }
        }

        let basis_names: Vec<String> = free_indices
            .iter()
            .map(|&idx| ambient_monomials[idx].display(&vars))
            .collect();
        let one_idx = mono_index[&Monomial::one(d)];
        let one: Vec<C> = (0..q_dim)
            .map(|r| ambient_to_quotient[r][one_idx].clone())
            .collect();
        let mut mul_table = vec![vec![vec![z.clone(); q_dim]; q_dim]; q_dim];
        for i in 0..q_dim {
            let mi = &ambient_monomials[free_indices[i]];
            for j in 0..q_dim {
                let mj = &ambient_monomials[free_indices[j]];
                if mi.total_degree() + mj.total_degree() <= max_deg as u64 {
                    let prod = mi.mul(mj);
                    if let Some(&col) = mono_index.get(&prod) {
                        for r in 0..q_dim {
                            mul_table[i][j][r] = ambient_to_quotient[r][col].clone();
                        }
                    }
                }
            }
        }

        let algebra = FiniteAlgebra {
            basis_names,
            zero_coeff: z,
            one,
            mul_table,
        };
        Ok(Self {
            vars,
            base_point: base_point.to_vec(),
            max_deg,
            ambient_monomials,
            free_indices,
            ambient_to_quotient,
            algebra,
        })
    }

    /// 元の座標 `z` 上の多項式 `poly` を `A / m^{r+1}` へ射影する（`z -> a + w`, mod `I_O + m^{r+1}`）。
    pub fn project_poly(&self, poly: &Poly<C>) -> Result<Vec<C>, AlgebraError> {
        let d = self.vars.len();
        if poly.num_vars() != d {
            return Err(AlgebraError::ArityMismatch {
                expected: d,
                actual: poly.num_vars(),
            });
        }
        let shift_polys = make_shift_polys(d, &self.base_point, &self.algebra.zero_coeff);
        let shifted = poly
            .substitute(&shift_polys)?
            .truncate_degree(self.max_deg as u64);
        let q_dim = self.algebra.dim();
        let mut out = vec![self.algebra.zero_coeff.zero_like(); q_dim];
        for (mono, coeff) in shifted.terms() {
            if let Some(col) = self.ambient_monomials.iter().position(|m| m == mono) {
                for (dst, row) in out.iter_mut().zip(&self.ambient_to_quotient) {
                    let entry = &row[col];
                    if !entry.coeff_is_zero() {
                        *dst = dst.add_ref(&coeff.mul_ref(entry));
                    }
                }
            }
        }
        Ok(out)
    }
}

/// 全次数 `<= max_deg` の全単項式を次数昇順・辞書順で列挙する（次元上限 `max_dim` 超過時は `OutOfScope`）。
pub fn enumerate_monomials_up_to(
    num_vars: usize,
    max_deg: usize,
    max_dim: usize,
) -> Result<Vec<Monomial>, AlgebraError> {
    let mut out = Vec::new();
    let mut current = vec![0u32; num_vars];
    for deg in 0..=max_deg {
        enumerate_degree_rec(num_vars, 0, deg as u32, &mut current, &mut out, max_dim)?;
    }
    Ok(out)
}

fn enumerate_degree_rec(
    num_vars: usize,
    pos: usize,
    remaining: u32,
    current: &mut [u32],
    out: &mut Vec<Monomial>,
    max_dim: usize,
) -> Result<(), AlgebraError> {
    if pos == num_vars {
        if remaining == 0 {
            if out.len() >= max_dim {
                return Err(AlgebraError::OutOfScope {
                    detail: format!(
                        "local Artin quotient dimension exceeds safety bound ({max_dim})"
                    ),
                });
            }
            out.push(Monomial::from_exps(current.to_vec()));
        }
        return Ok(());
    }
    if pos + 1 == num_vars {
        current[pos] = remaining;
        if out.len() >= max_dim {
            return Err(AlgebraError::OutOfScope {
                detail: format!("local Artin quotient dimension exceeds safety bound ({max_dim})"),
            });
        }
        out.push(Monomial::from_exps(current.to_vec()));
        current[pos] = 0;
        return Ok(());
    }
    for e in 0..=remaining {
        current[pos] = e;
        enumerate_degree_rec(num_vars, pos + 1, remaining - e, current, out, max_dim)?;
    }
    current[pos] = 0;
    Ok(())
}

fn make_shift_polys<C: RingCoeff>(d: usize, base_point: &[C], zero_coeff: &C) -> Vec<Poly<C>> {
    (0..d)
        .map(|i| {
            let mut p = Poly::var(d, i, zero_coeff.clone());
            if !base_point[i].coeff_is_zero() {
                p.add_term(Monomial::one(d), base_point[i].clone());
            }
            p
        })
        .collect()
}
