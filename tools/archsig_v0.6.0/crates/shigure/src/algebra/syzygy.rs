//! 原始多項式族の全 syzygy 生成族計算（Schreyer 構成・$\mathbb{Q}/\mathbb{F}_p$・$\mathbb{Z}$ 検証済み族）と
//! 形式偏微分 Jacobian 計算（G-141 E2・E8・H2–H3）。

use crate::algebra::MonomialOrder;
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Monomial, Poly, VarOrder};
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};
use std::collections::BTreeSet;

/// Schreyer / Buchberger S-pair 計算の既定安全上限。
pub const DEFAULT_MAX_SYZYGY_PAIRS: usize = 4_096;

/// 体係数（`Q`・`F_p`）に対する共通逆元トレイト。
pub trait FieldCoeff: RingCoeff {
    fn coeff_inv(&self) -> Option<Self>;
}

impl FieldCoeff for Rat {
    fn coeff_inv(&self) -> Option<Self> {
        self.inv()
    }
}

impl FieldCoeff for FpElem {
    fn coeff_inv(&self) -> Option<Self> {
        self.inv()
    }
}

/// 原始多項式族 `(f_1, ..., f_r)` の全 syzygy 加群 `S = ker(B^r -> J)` の生成族。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SyzygyModule<C: RingCoeff> {
    pub vars: VarOrder,
    pub originals: Vec<Poly<C>>,
    /// 各要素 `s` は長さ `originals.len()` の多項式ベクトルで、`sum_i s[i] * originals[i] == 0`。
    pub generators: Vec<Vec<Poly<C>>>,
    /// 全生成元について多項式恒等式 `sum_i s[i] * originals[i] == 0` を独立検算した結果。
    pub verified: bool,
    /// 返却生成族が `ker(B^r -> J)` 全体を生成することが証明済みであるか。
    pub generating_certified: bool,
}

impl<C: RingCoeff> SyzygyModule<C> {
    /// 全生成元について多項式恒等式 `sum_i s[i] * f_i == 0` を独立検算する。
    pub fn verify_all(&self) -> Result<bool, AlgebraError> {
        let n = self.vars.len();
        let zero_coeff = match self.originals.first() {
            Some(p) => p.zero_coeff().clone(),
            None => return Ok(self.generators.is_empty()),
        };
        for syz in &self.generators {
            if syz.len() != self.originals.len() {
                return Ok(false);
            }
            let mut acc = Poly::zero(n, zero_coeff.clone());
            for (s_i, f_i) in syz.iter().zip(&self.originals) {
                if !s_i.is_zero() && !f_i.is_zero() {
                    acc = acc.add(&s_i.checked_mul(f_i)?);
                }
            }
            if !acc.is_zero() {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

/// 原始多項式族 `(f_1, ..., f_r)` の形式偏微分による Jacobian 多項式行列 `r x num_vars` を返す。
pub fn jacobian_polys<C: RingCoeff>(
    polys: &[Poly<C>],
    num_vars: usize,
) -> Result<Vec<Vec<Poly<C>>>, AlgebraError> {
    let mut mat = Vec::with_capacity(polys.len());
    for f in polys {
        if f.num_vars() != num_vars {
            return Err(AlgebraError::ArityMismatch {
                expected: num_vars,
                actual: f.num_vars(),
            });
        }
        let mut row = Vec::with_capacity(num_vars);
        for v in 0..num_vars {
            row.push(f.partial_derivative(v)?);
        }
        mat.push(row);
    }
    Ok(mat)
}

#[derive(Clone, Debug)]
struct FieldTracked<C: FieldCoeff> {
    poly: Poly<C>,
    cofactors: Vec<Poly<C>>,
}

/// 体 `K`（`Q` または `F_p`）上の原始多項式族 `F = (f_1, ..., f_r)` の全 syzygy 生成族を
/// Gröbner 基底と Schreyer の定理により厳密計算する（G-141 E2）。
pub fn compute_syzygies_field<C: FieldCoeff>(
    originals: &[Poly<C>],
    vars: VarOrder,
    order: MonomialOrder,
    max_pairs: usize,
) -> Result<SyzygyModule<C>, AlgebraError> {
    let n = vars.len();
    let r = originals.len();
    for f in originals {
        if f.num_vars() != n {
            return Err(AlgebraError::ArityMismatch {
                expected: n,
                actual: f.num_vars(),
            });
        }
    }
    if r == 0 {
        return Ok(SyzygyModule {
            vars,
            originals: Vec::new(),
            generators: Vec::new(),
            verified: true,
            generating_certified: true,
        });
    }
    let zero_c = originals[0].zero_coeff().clone();
    for f in originals.iter().skip(1) {
        if !zero_c.same_ring(f.zero_coeff()) {
            return Err(AlgebraError::DomainMismatch {
                expected: format!("{zero_c:?}"),
                actual: format!("{:?}", f.zero_coeff()),
            });
        }
    }
    let zero_p = Poly::zero(n, zero_c.clone());
    let one_p = Poly::one(n, zero_c.clone());

    // 1. cofactor 追跡付き Gröbner 基底 G = A * F を構成する。
    let basis = compute_tracked_gb(originals, n, &zero_c, order, max_pairs)?;

    // 2. 各原始多項式 f_i を G で割って B_{i,*} を得る: f_i = sum_a B_{i,a} * g_a。
    //    I_r - B * A の各行は Syz(F) に属する。
    let mut raw_syzs: Vec<Vec<Poly<C>>> = Vec::new();
    for (i, f_i) in originals.iter().enumerate() {
        if f_i.is_zero() {
            let mut e_i = vec![zero_p.clone(); r];
            e_i[i] = one_p.clone();
            raw_syzs.push(e_i);
            continue;
        }
        let (rem, b_row) = divide_field(f_i, &basis, &zero_c, order)?;
        if !rem.is_zero() {
            return Err(AlgebraError::OutOfScope {
                detail: "internal Groebner division invariant violated while expressing originals"
                    .to_owned(),
            });
        }
        // e_i - sum_a b_row[a] * basis[a].cofactors
        let mut syz = vec![zero_p.clone(); r];
        syz[i] = one_p.clone();
        for (b_ia, g_a) in b_row.iter().zip(&basis) {
            if b_ia.is_zero() {
                continue;
            }
            for (dst, a_aj) in syz.iter_mut().zip(&g_a.cofactors) {
                if !a_aj.is_zero() {
                    *dst = dst.sub(&b_ia.checked_mul(a_aj)?);
                }
            }
        }
        raw_syzs.push(syz);
    }

    // 3. Schreyer の定理: G の全ペア (a < b) の S-多項式簡約から Syz(G) を生成し、A で Syz(F) へ持ち上げる。
    //    注意: 先頭単項式が互いに素なペアも Koszul syzygy を与えるため省略してはならない。
    let m = basis.len();
    let mut checked_pairs = 0usize;
    for a in 0..m {
        for b in (a + 1)..m {
            checked_pairs += 1;
            if checked_pairs > max_pairs {
                return Err(AlgebraError::OutOfScope {
                    detail: format!("Schreyer syzygy pair generation exceeded limit ({max_pairs})"),
                });
            }
            let (lm_a, lc_a) = basis[a]
                .poly
                .leading_term(order)
                .expect("GB element is nonzero");
            let (lm_b, lc_b) = basis[b]
                .poly
                .leading_term(order)
                .expect("GB element is nonzero");
            let lcm = lm_a.lcm(lm_b);
            let m_a = lcm.div_exact(lm_a).expect("lcm divisible by lm_a");
            let m_b = lcm.div_exact(lm_b).expect("lcm divisible by lm_b");
            let inv_a = lc_a.coeff_inv().expect("nonzero field coeff has inverse");
            let inv_b = lc_b.coeff_inv().expect("nonzero field coeff has inverse");

            let s_poly = basis[a]
                .poly
                .checked_mul_term(&m_a, &inv_a)?
                .sub(&basis[b].poly.checked_mul_term(&m_b, &inv_b)?);
            let (rem, q_row) = divide_field(&s_poly, &basis, &zero_c, order)?;
            if !rem.is_zero() {
                return Err(AlgebraError::OutOfScope {
                    detail: "internal Groebner basis S-polynomial did not reduce to zero"
                        .to_owned(),
                });
            }
            // u = (inv_a * m_a) e_a - (inv_b * m_b) e_b - sum_c q_row[c] e_c
            let mut u = vec![zero_p.clone(); m];
            u[a].try_add_term(m_a, inv_a)?;
            u[b].try_add_term(m_b, inv_b.neg_ref())?;
            for (dst, q_c) in u.iter_mut().zip(&q_row) {
                if !q_c.is_zero() {
                    *dst = dst.sub(q_c);
                }
            }
            // Lift u * A into Syz(F)
            let mut lifted = vec![zero_p.clone(); r];
            for (u_c, g_c) in u.iter().zip(&basis) {
                if u_c.is_zero() {
                    continue;
                }
                for (dst, a_cj) in lifted.iter_mut().zip(&g_c.cofactors) {
                    if !a_cj.is_zero() {
                        *dst = dst.add(&u_c.checked_mul(a_cj)?);
                    }
                }
            }
            raw_syzs.push(lifted);
        }
    }

    // 4. 零ベクトル・重複を除去して正規化・独立検算する。
    let generators = dedup_nonzero_syzygies(raw_syzs);
    let mut module = SyzygyModule {
        vars,
        originals: originals.to_vec(),
        generators,
        verified: false,
        generating_certified: true,
    };
    module.verified = module.verify_all()?;
    if !module.verified {
        return Err(AlgebraError::OutOfScope {
            detail: "computed syzygy failed polynomial identity verification".to_owned(),
        });
    }
    Ok(module)
}

/// 整数環 `Z[x]` 上の原始多項式族について、生成性が証明可能な族（単項式族・共通因子スカラー倍族・
/// 単位可逆線形族）の全 syzygy 生成族を計算する。
/// 生成性を保証できない一般非線形 `Z[x]` 族は誤った部分族を返さず `OutOfScope` を返す（G-141 E2・H2）。
pub fn compute_syzygies_z(
    originals: &[Poly<BigInt>],
    vars: VarOrder,
) -> Result<SyzygyModule<BigInt>, AlgebraError> {
    let n = vars.len();
    let r = originals.len();
    for f in originals {
        if f.num_vars() != n {
            return Err(AlgebraError::ArityMismatch {
                expected: n,
                actual: f.num_vars(),
            });
        }
    }
    let zero_p = Poly::zero(n, BigInt::zero());
    let one_p = Poly::one(n, BigInt::zero());
    if r == 0 {
        return Ok(SyzygyModule {
            vars,
            originals: Vec::new(),
            generators: Vec::new(),
            verified: true,
            generating_certified: true,
        });
    }

    let mut raw_syzs: Vec<Vec<Poly<BigInt>>> = Vec::new();
    let mut nonzero_indices = Vec::new();
    for (i, f) in originals.iter().enumerate() {
        if f.is_zero() {
            let mut e_i = vec![zero_p.clone(); r];
            e_i[i] = one_p.clone();
            raw_syzs.push(e_i);
        } else {
            nonzero_indices.push(i);
        }
    }

    if nonzero_indices.len() <= 1 {
        // 非零元が 0 個または 1 個なら整域 Z[x] 上で残る syzygy は零のみ。
        return finalize_z_syzygies(vars, originals, raw_syzs);
    }

    // Case 1: 全非零元が単項式 c_i * m_i（UFD Z[x] ではペアごとの最小 syzygy が全体を生成）。
    if nonzero_indices
        .iter()
        .all(|&i| originals[i].terms().len() == 1)
    {
        for a_pos in 0..nonzero_indices.len() {
            for b_pos in (a_pos + 1)..nonzero_indices.len() {
                let i = nonzero_indices[a_pos];
                let j = nonzero_indices[b_pos];
                let (m_i, c_i) = originals[i].terms().iter().next().expect("single term");
                let (m_j, c_j) = originals[j].terms().iter().next().expect("single term");
                let lcm_m = m_i.lcm(m_j);
                let q_mi = lcm_m.div_exact(m_i).expect("lcm divisible");
                let q_mj = lcm_m.div_exact(m_j).expect("lcm divisible");
                let lcm_c = c_i.lcm(c_j);
                let q_ci = &lcm_c / c_i;
                let q_cj = -(&lcm_c / c_j);
                let mut syz = vec![zero_p.clone(); r];
                syz[i].add_term(q_mi, q_ci);
                syz[j].add_term(q_mj, q_cj);
                raw_syzs.push(syz);
            }
        }
        return finalize_z_syzygies(vars, originals, raw_syzs);
    }

    // Case 2: 全非零元が共通原始多項式 h の整数倍 f_i = c_i * h（整域なので ker(Z^r -> Z) が生成）。
    if let Some(coeffs) = extract_common_primitive_multiples(originals, &nonzero_indices) {
        let row = vec![coeffs];
        let rhs = vec![BigInt::zero()];
        match solve_affine_z(&row, &rhs, nonzero_indices.len())? {
            AffineSolutionZ::Consistent { kernel_basis, .. } => {
                for vec_z in kernel_basis {
                    let mut syz = vec![zero_p.clone(); r];
                    for (&orig_idx, c) in nonzero_indices.iter().zip(vec_z) {
                        if !c.is_zero() {
                            syz[orig_idx] = Poly::constant(n, c);
                        }
                    }
                    raw_syzs.push(syz);
                }
                return finalize_z_syzygies(vars, originals, raw_syzs);
            }
            AffineSolutionZ::Inconsistent { .. } => {
                return Err(AlgebraError::OutOfScope {
                    detail: "homogeneous Z linear system unexpectedly inconsistent".to_owned(),
                });
            }
        }
    }

    // Case 3: 全非零元が斉次 1 次式かつ Smith 対角がすべて 1（単位可逆線形変換で正則列へ還元可能）。
    if nonzero_indices
        .iter()
        .all(|&i| originals[i].terms().keys().all(|m| m.total_degree() == 1))
        && let Some(linear_syzs) = try_unimodular_linear_syzygies_z(originals, &nonzero_indices, n)?
    {
        raw_syzs.extend(linear_syzs);
        return finalize_z_syzygies(vars, originals, raw_syzs);
    }

    Err(AlgebraError::OutOfScope {
        detail: "full syzygy generation over Z is only certified for monomial, common-factor, and unimodular linear families (G-141 E2)".to_owned(),
    })
}

fn finalize_z_syzygies(
    vars: VarOrder,
    originals: &[Poly<BigInt>],
    raw_syzs: Vec<Vec<Poly<BigInt>>>,
) -> Result<SyzygyModule<BigInt>, AlgebraError> {
    let generators = dedup_nonzero_syzygies(raw_syzs);
    let mut module = SyzygyModule {
        vars,
        originals: originals.to_vec(),
        generators,
        verified: false,
        generating_certified: true,
    };
    module.verified = module.verify_all()?;
    if !module.verified {
        return Err(AlgebraError::OutOfScope {
            detail: "computed Z syzygy failed polynomial identity verification".to_owned(),
        });
    }
    Ok(module)
}

fn poly_content_z(poly: &Poly<BigInt>) -> BigInt {
    let mut g = BigInt::zero();
    for c in poly.terms().values() {
        g = g.gcd(c);
    }
    if g.is_zero() {
        BigInt::one()
    } else {
        g
    }
}

fn primitive_part_z(poly: &Poly<BigInt>) -> (BigInt, Poly<BigInt>) {
    let content = poly_content_z(poly);
    let sign = poly
        .terms()
        .values()
        .next()
        .is_some_and(|c| *c < BigInt::zero());
    let signed_content = if sign { -content } else { content };
    let mut prim = Poly::zero(poly.num_vars(), BigInt::zero());
    for (m, c) in poly.terms() {
        prim.add_term(m.clone(), c / &signed_content);
    }
    (signed_content, prim)
}

fn extract_common_primitive_multiples(
    originals: &[Poly<BigInt>],
    nonzero_indices: &[usize],
) -> Option<Vec<BigInt>> {
    let (first_c, first_prim) = primitive_part_z(&originals[nonzero_indices[0]]);
    let mut coeffs = vec![first_c];
    for &idx in nonzero_indices.iter().skip(1) {
        let (c, prim) = primitive_part_z(&originals[idx]);
        if prim != first_prim {
            return None;
        }
        coeffs.push(c);
    }
    Some(coeffs)
}

fn try_unimodular_linear_syzygies_z(
    originals: &[Poly<BigInt>],
    nonzero_indices: &[usize],
    num_vars: usize,
) -> Result<Option<Vec<Vec<Poly<BigInt>>>>, AlgebraError> {
    let r = originals.len();
    let k = nonzero_indices.len();
    // 転置行列 M (num_vars x k): 各列が originals[idx] の 1 次係数。
    let mut mat = vec![vec![BigInt::zero(); k]; num_vars];
    for (col, &orig_idx) in nonzero_indices.iter().enumerate() {
        for (m, c) in originals[orig_idx].terms() {
            if let Some((var_idx, _)) = m.exps().iter().enumerate().find(|(_, e)| **e == 1) {
                mat[var_idx][col] = c.clone();
            }
        }
    }
    let rhs = vec![BigInt::zero(); num_vars];
    let sol = solve_affine_z(&mat, &rhs, k)?;
    let AffineSolutionZ::Consistent {
        kernel_basis,
        smith_diagonals,
        ..
    } = sol
    else {
        return Ok(None);
    };
    if !smith_diagonals.iter().all(One::is_one) {
        return Ok(None);
    }
    let zero_p = Poly::zero(num_vars, BigInt::zero());
    let mut out = Vec::new();
    // 定数係数 syzygy（Smith 核基底）
    for vec_z in kernel_basis {
        let mut syz = vec![zero_p.clone(); r];
        for (&orig_idx, c) in nonzero_indices.iter().zip(vec_z) {
            if !c.is_zero() {
                syz[orig_idx] = Poly::constant(num_vars, c);
            }
        }
        out.push(syz);
    }
    // Koszul syzygy f_j e_i - f_i e_j（独立線形列の正則列 syzygy を生成）
    for a in 0..k {
        for b in (a + 1)..k {
            let i = nonzero_indices[a];
            let j = nonzero_indices[b];
            let mut syz = vec![zero_p.clone(); r];
            syz[i] = originals[j].clone();
            syz[j] = originals[i].neg();
            out.push(syz);
        }
    }
    Ok(Some(out))
}

fn dedup_nonzero_syzygies<C: RingCoeff>(raw: Vec<Vec<Poly<C>>>) -> Vec<Vec<Poly<C>>> {
    let mut out: Vec<Vec<Poly<C>>> = Vec::new();
    for syz in raw {
        if syz.iter().all(Poly::is_zero) {
            continue;
        }
        if !out.contains(&syz) {
            out.push(syz);
        }
    }
    out
}

fn compute_tracked_gb<C: FieldCoeff>(
    originals: &[Poly<C>],
    n: usize,
    zero_c: &C,
    order: MonomialOrder,
    max_pairs: usize,
) -> Result<Vec<FieldTracked<C>>, AlgebraError> {
    let r = originals.len();
    let zero_p = Poly::zero(n, zero_c.clone());
    let one_p = Poly::one(n, zero_c.clone());

    let mut basis: Vec<FieldTracked<C>> = Vec::new();
    let mut basis_lms: Vec<Monomial> = Vec::new();
    for (i, f) in originals.iter().enumerate() {
        if f.is_zero() {
            continue;
        }
        let mut cofactors = vec![zero_p.clone(); r];
        cofactors[i] = one_p.clone();
        let tracked = make_monic_field(
            FieldTracked {
                poly: f.clone(),
                cofactors,
            },
            order,
        );
        let Some((lm, _)) = tracked.poly.leading_term(order) else {
            continue;
        };
        let lm = lm.clone();
        if lm.is_one() {
            return Ok(vec![tracked]);
        }
        basis.push(tracked);
        basis_lms.push(lm);
    }

    let mut pairs: Vec<(usize, usize, u64)> = Vec::new();
    for i in 0..basis.len() {
        for j in (i + 1)..basis.len() {
            pairs.push((i, j, basis_lms[i].lcm(&basis_lms[j]).total_degree()));
        }
    }
    let mut handled: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut processed = 0usize;

    while let Some((i, j)) = pop_min_pair(&mut pairs) {
        processed += 1;
        if processed > max_pairs {
            return Err(AlgebraError::OutOfScope {
                detail: format!("Groebner syzygy computation exceeded pair limit ({max_pairs})"),
            });
        }
        let key = if i < j { (i, j) } else { (j, i) };
        let lm_i = &basis_lms[i];
        let lm_j = &basis_lms[j];
        if lm_i.gcd_is_one(lm_j) {
            handled.insert(key);
            continue;
        }
        let lcm_ij = lm_i.lcm(lm_j);
        if chain_criterion(&basis_lms, i, j, &lcm_ij, &handled) {
            handled.insert(key);
            continue;
        }
        let s_poly = s_polynomial_field(&basis[i], &basis[j], order)?;
        let reduced = reduce_tracked_field(&s_poly, &basis, zero_c, order)?;
        handled.insert(key);
        if !reduced.poly.is_zero() {
            let monic = make_monic_field(reduced, order);
            let Some((new_lm, _)) = monic.poly.leading_term(order) else {
                continue;
            };
            let new_lm = new_lm.clone();
            let is_unit = new_lm.is_one();
            let new_idx = basis.len();
            for (prev, prev_lm) in basis_lms.iter().enumerate() {
                pairs.push((prev, new_idx, prev_lm.lcm(&new_lm).total_degree()));
            }
            basis.push(monic);
            basis_lms.push(new_lm);
            if is_unit {
                let unit = basis.pop().expect("unit polynomial pushed");
                return Ok(vec![unit]);
            }
        }
    }
    Ok(basis)
}

fn make_monic_field<C: FieldCoeff>(
    mut tracked: FieldTracked<C>,
    order: MonomialOrder,
) -> FieldTracked<C> {
    let Some((_, lc)) = tracked.poly.leading_term(order) else {
        return tracked;
    };
    if lc.coeff_is_one() {
        return tracked;
    }
    let inv = lc.coeff_inv().expect("leading coefficient is nonzero");
    tracked.poly = tracked.poly.scale(&inv);
    for c in &mut tracked.cofactors {
        *c = c.scale(&inv);
    }
    tracked
}

fn s_polynomial_field<C: FieldCoeff>(
    a: &FieldTracked<C>,
    b: &FieldTracked<C>,
    order: MonomialOrder,
) -> Result<FieldTracked<C>, AlgebraError> {
    let (lm_a, lc_a) = a
        .poly
        .leading_term(order)
        .expect("nonzero tracked polynomial");
    let (lm_b, lc_b) = b
        .poly
        .leading_term(order)
        .expect("nonzero tracked polynomial");
    let lcm = lm_a.lcm(lm_b);
    let m_a = lcm.div_exact(lm_a).expect("lcm divisible");
    let m_b = lcm.div_exact(lm_b).expect("lcm divisible");
    let inv_a = lc_a.coeff_inv().expect("nonzero coeff");
    let inv_b = lc_b.coeff_inv().expect("nonzero coeff");

    let poly = a
        .poly
        .checked_mul_term(&m_a, &inv_a)?
        .sub(&b.poly.checked_mul_term(&m_b, &inv_b)?);
    let mut cofactors = Vec::with_capacity(a.cofactors.len());
    for (ca, cb) in a.cofactors.iter().zip(&b.cofactors) {
        let left = ca.checked_mul_term(&m_a, &inv_a)?;
        let right = cb.checked_mul_term(&m_b, &inv_b)?;
        cofactors.push(left.sub(&right));
    }
    Ok(FieldTracked { poly, cofactors })
}

fn reduce_tracked_field<C: FieldCoeff>(
    target: &FieldTracked<C>,
    basis: &[FieldTracked<C>],
    zero_c: &C,
    order: MonomialOrder,
) -> Result<FieldTracked<C>, AlgebraError> {
    let n = target.poly.num_vars();
    let mut p = target.poly.clone();
    let mut cofactors = target.cofactors.clone();
    let mut rem = Poly::zero(n, zero_c.clone());

    while let Some((lm_p, lc_p)) = p.leading_term(order) {
        let lm_p = lm_p.clone();
        let lc_p = lc_p.clone();
        let mut divided = false;
        for g in basis {
            if let Some((lm_g, lc_g)) = g.poly.leading_term(order)
                && let Some(q_mono) = lm_p.div_exact(lm_g)
            {
                let inv_g = lc_g.coeff_inv().expect("divisor leading coeff nonzero");
                let q_coeff = lc_p.mul_ref(&inv_g);
                p.checked_sub_mul_term_assign(&g.poly, &q_mono, &q_coeff)?;
                for (acc, gc) in cofactors.iter_mut().zip(&g.cofactors) {
                    if !gc.is_zero() {
                        acc.checked_sub_mul_term_assign(gc, &q_mono, &q_coeff)?;
                    }
                }
                divided = true;
                break;
            }
        }
        if !divided {
            p.remove_term(&lm_p);
            rem.add_term(lm_p, lc_p);
        }
    }

    Ok(FieldTracked {
        poly: rem,
        cofactors,
    })
}

fn divide_field<C: FieldCoeff>(
    target: &Poly<C>,
    basis: &[FieldTracked<C>],
    zero_c: &C,
    order: MonomialOrder,
) -> Result<(Poly<C>, Vec<Poly<C>>), AlgebraError> {
    let n = target.num_vars();
    let mut p = target.clone();
    let mut rem = Poly::zero(n, zero_c.clone());
    let mut quotients = vec![Poly::zero(n, zero_c.clone()); basis.len()];

    while let Some((lm_p, lc_p)) = p.leading_term(order) {
        let lm_p = lm_p.clone();
        let lc_p = lc_p.clone();
        let mut divided = false;
        for (idx, g) in basis.iter().enumerate() {
            if let Some((lm_g, lc_g)) = g.poly.leading_term(order)
                && let Some(q_mono) = lm_p.div_exact(lm_g)
            {
                let inv_g = lc_g.coeff_inv().expect("divisor leading coeff nonzero");
                let q_coeff = lc_p.mul_ref(&inv_g);
                p.checked_sub_mul_term_assign(&g.poly, &q_mono, &q_coeff)?;
                quotients[idx].add_term(q_mono, q_coeff);
                divided = true;
                break;
            }
        }
        if !divided {
            p.remove_term(&lm_p);
            rem.add_term(lm_p, lc_p);
        }
    }

    Ok((rem, quotients))
}

/// 体 `K`（`Q` または `F_p`）上の多項式 `target` が `gens` の生成する ideal に属するか判定し、
/// 属する場合は `target = sum_i c_i * gens[i]` を満たす厳密 cofactor `c_i` を返す。
pub fn ideal_membership_field<C: FieldCoeff>(
    target: &Poly<C>,
    gens: &[Poly<C>],
    vars: &VarOrder,
    order: MonomialOrder,
    max_pairs: usize,
) -> Result<Option<Vec<Poly<C>>>, AlgebraError> {
    let n = vars.len();
    if target.num_vars() != n {
        return Err(AlgebraError::ArityMismatch {
            expected: n,
            actual: target.num_vars(),
        });
    }
    for g in gens {
        if g.num_vars() != n {
            return Err(AlgebraError::ArityMismatch {
                expected: n,
                actual: g.num_vars(),
            });
        }
    }
    let zero_c = target.zero_coeff().clone();
    for g in gens {
        if !zero_c.same_ring(g.zero_coeff()) {
            return Err(AlgebraError::DomainMismatch {
                expected: format!("{zero_c:?}"),
                actual: format!("{:?}", g.zero_coeff()),
            });
        }
    }
    if target.is_zero() {
        return Ok(Some(vec![Poly::zero(n, zero_c); gens.len()]));
    }
    if gens.is_empty() {
        return Ok(None);
    }
    let basis = compute_tracked_gb(gens, n, &zero_c, order, max_pairs)?;
    let (rem, q_row) = divide_field(target, &basis, &zero_c, order)?;
    if !rem.is_zero() {
        return Ok(None);
    }
    let mut cofactors = vec![Poly::zero(n, zero_c.clone()); gens.len()];
    for (q_a, g_a) in q_row.iter().zip(&basis) {
        if q_a.is_zero() {
            continue;
        }
        for (dst, a_aj) in cofactors.iter_mut().zip(&g_a.cofactors) {
            if !a_aj.is_zero() {
                *dst = dst.add(&q_a.checked_mul(a_aj)?);
            }
        }
    }
    let mut acc = Poly::zero(n, zero_c);
    for (c, g) in cofactors.iter().zip(gens) {
        if !c.is_zero() && !g.is_zero() {
            acc = acc.add(&c.checked_mul(g)?);
        }
    }
    if acc != *target {
        return Err(AlgebraError::OutOfScope {
            detail: "internal ideal membership cofactor reconstruction invariant violated"
                .to_owned(),
        });
    }
    Ok(Some(cofactors))
}

fn pop_min_pair(pairs: &mut Vec<(usize, usize, u64)>) -> Option<(usize, usize)> {
    if pairs.is_empty() {
        return None;
    }
    let mut best_pos = 0usize;
    let mut best_deg = pairs[0].2;
    for (pos, &(_, _, deg)) in pairs.iter().enumerate().skip(1) {
        if deg < best_deg {
            best_deg = deg;
            best_pos = pos;
        }
    }
    let (i, j, _) = pairs.swap_remove(best_pos);
    Some((i, j))
}

fn chain_criterion(
    basis_lms: &[Monomial],
    i: usize,
    j: usize,
    lcm_ij: &Monomial,
    handled: &BTreeSet<(usize, usize)>,
) -> bool {
    for (k, lm_k) in basis_lms.iter().enumerate() {
        if k == i || k == j {
            continue;
        }
        if lm_k.divides(lcm_ij) {
            let p_ik = if i < k { (i, k) } else { (k, i) };
            let p_jk = if j < k { (j, k) } else { (k, j) };
            if handled.contains(&p_ik) && handled.contains(&p_jk) {
                return true;
            }
        }
    }
    false
}
