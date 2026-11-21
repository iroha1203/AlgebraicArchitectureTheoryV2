//! Q 上の Gröbner 基底、witness 付き ideal 所属判定、および Rabinowitsch 可逆条件（G-141 D5 / AC5(a)）。

use crate::algebra::MonomialOrder;
use crate::algebra::poly::{AlgebraError, Monomial, Poly, VarOrder};
use crate::algebra::scalar::Rat;
use crate::ir::result::EmptyWitness;
use std::collections::BTreeSet;

/// Buchberger 反復の安全上限（超過時は誤判定せず `AlgebraError::OutOfScope` を返す）。
pub const DEFAULT_MAX_BUCHBERGER_PAIRS: usize = 4_096;

/// 元の生成元列 `F = [f_0, ..., f_{k-1}]` に対する表現 `poly = sum_i cofactors[i] * f_i` を保持する元。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrackedPoly {
    pub poly: Poly<Rat>,
    pub cofactors: Vec<Poly<Rat>>,
}

/// Q 上の cofactor 追跡付き Gröbner 基底。
#[derive(Clone, Debug)]
pub struct GroebnerBasis {
    vars: VarOrder,
    order: MonomialOrder,
    originals: Vec<Poly<Rat>>,
    basis: Vec<TrackedPoly>,
}

/// ideal 所属判定の結果と検算済み witness（`target = sum_i cofactors[i] * originals[i] + remainder`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MembershipResult {
    pub is_member: bool,
    pub remainder: Poly<Rat>,
    pub cofactors: Vec<Poly<Rat>>,
    pub verified: bool,
}

/// Rabinowitsch 可逆条件 `V(equations) ∩ D(invertibles)` の解析結果。
#[derive(Clone, Debug)]
pub struct RabinowitschResult {
    /// 元の変数空間での消去済み残差（補助変数を含まない基底元）。
    pub parameter_equations: Vec<Poly<Rat>>,
    /// `1 in I` なら代数閉包上で空。
    pub is_empty_over_closure: bool,
    /// 空のときの検算済み witness `1 = sum h_i f_i`（拡大環上の生成元と係数）。
    pub empty_witness: Option<EmptyWitness>,
    /// 拡大環の変数順序。
    pub extended_vars: VarOrder,
    /// 拡大環の Gröbner 基底。
    pub basis: GroebnerBasis,
}

impl GroebnerBasis {
    /// 与えられた生成元列から cofactor 追跡付きの簡約 Gröbner 基底を構成する。
    pub fn compute(
        generators: &[Poly<Rat>],
        vars: VarOrder,
        order: MonomialOrder,
    ) -> Result<Self, AlgebraError> {
        Self::compute_with_limit(generators, vars, order, DEFAULT_MAX_BUCHBERGER_PAIRS)
    }

    pub fn compute_with_limit(
        generators: &[Poly<Rat>],
        vars: VarOrder,
        order: MonomialOrder,
        max_pairs: usize,
    ) -> Result<Self, AlgebraError> {
        let n = vars.len();
        for g in generators {
            if g.num_vars() != n {
                return Err(AlgebraError::ArityMismatch {
                    expected: n,
                    actual: g.num_vars(),
                });
            }
        }
        let k = generators.len();
        let zero_p = Poly::zero(n, Rat::zero());
        let one_p = Poly::one(n, Rat::zero());

        let mut basis: Vec<TrackedPoly> = Vec::new();
        let mut basis_lms: Vec<Monomial> = Vec::new();
        for (i, g) in generators.iter().enumerate() {
            if g.is_zero() {
                continue;
            }
            let mut cofactors = vec![zero_p.clone(); k];
            cofactors[i] = one_p.clone();
            let tracked = make_monic(
                TrackedPoly {
                    poly: g.clone(),
                    cofactors,
                },
                order,
            );
            let Some((lm, _)) = tracked.poly.leading_term(order) else {
                continue;
            };
            let lm = lm.clone();
            if lm.is_one() {
                return Ok(Self {
                    vars,
                    order,
                    originals: generators.to_vec(),
                    basis: vec![tracked],
                });
            }
            basis.push(tracked);
            basis_lms.push(lm);
        }

        let mut pairs: Vec<(usize, usize, u64)> = Vec::new();
        for i in 0..basis.len() {
            for j in (i + 1)..basis.len() {
                let deg = basis_lms[i].lcm(&basis_lms[j]).total_degree();
                pairs.push((i, j, deg));
            }
        }
        let mut handled: BTreeSet<(usize, usize)> = BTreeSet::new();

        let mut processed = 0usize;
        while let Some((i, j)) = pop_min_degree_pair(&mut pairs) {
            processed += 1;
            if processed > max_pairs {
                return Err(AlgebraError::OutOfScope {
                    detail: format!("Groebner basis computation exceeded pair limit ({max_pairs})"),
                });
            }
            let pair_key = if i < j { (i, j) } else { (j, i) };
            let lm_i = &basis_lms[i];
            let lm_j = &basis_lms[j];
            // Buchberger 第 1 基準（先頭単項式が互いに素なら S 多項式は 0 へ簡約される）。
            if lm_i.gcd_is_one(lm_j) {
                handled.insert(pair_key);
                continue;
            }
            // Buchberger 第 2 基準（既処理ペアのみを参照するため循環スキップ不能）。
            let lcm_ij = lm_i.lcm(lm_j);
            if chain_criterion_applies(&basis_lms, i, j, &lcm_ij, &handled) {
                handled.insert(pair_key);
                continue;
            }

            let s_poly = s_polynomial(&basis[i], &basis[j], order)?;
            let reduced = reduce_tracked(&s_poly, &basis, order)?;
            handled.insert(pair_key);
            if !reduced.poly.is_zero() {
                let monic = make_monic(reduced, order);
                let Some((new_lm, _)) = monic.poly.leading_term(order) else {
                    continue;
                };
                let new_lm = new_lm.clone();
                let is_unit = new_lm.is_one();
                let new_idx = basis.len();
                for (prev, prev_lm) in basis_lms.iter().enumerate() {
                    let deg = prev_lm.lcm(&new_lm).total_degree();
                    pairs.push((prev, new_idx, deg));
                }
                basis.push(monic);
                basis_lms.push(new_lm);
                if is_unit {
                    let unit = basis.pop().expect("unit polynomial was just pushed");
                    return Ok(Self {
                        vars,
                        order,
                        originals: generators.to_vec(),
                        basis: vec![unit],
                    });
                }
            }
        }

        let reduced_basis = inter_reduce(basis, order)?;
        Ok(Self {
            vars,
            order,
            originals: generators.to_vec(),
            basis: reduced_basis,
        })
    }

    pub fn vars(&self) -> &VarOrder {
        &self.vars
    }

    pub fn order(&self) -> MonomialOrder {
        self.order
    }

    pub fn originals(&self) -> &[Poly<Rat>] {
        &self.originals
    }

    pub fn basis_polys(&self) -> Vec<&Poly<Rat>> {
        self.basis.iter().map(|t| &t.poly).collect()
    }

    pub fn contains_one(&self) -> bool {
        self.basis.iter().any(|t| {
            t.poly
                .leading_term(self.order)
                .is_some_and(|(m, _)| m.is_one())
        })
    }

    /// 対象多項式 `target` の ideal 所属を判定し、元の生成元に対する witness
    /// `target = sum_i cofactors[i] * originals[i] + remainder` を構成して独立検算する。
    pub fn membership(&self, target: &Poly<Rat>) -> Result<MembershipResult, AlgebraError> {
        if target.num_vars() != self.vars.len() {
            return Err(AlgebraError::ArityMismatch {
                expected: self.vars.len(),
                actual: target.num_vars(),
            });
        }
        let n = self.vars.len();
        let k = self.originals.len();
        let zero_p = Poly::zero(n, Rat::zero());
        let (remainder, quotients) = divide_with_quotients(target, &self.basis, self.order)?;

        let mut cofactors = vec![zero_p; k];
        for (q, g) in quotients.iter().zip(&self.basis) {
            if q.is_zero() {
                continue;
            }
            for (acc, gc) in cofactors.iter_mut().zip(&g.cofactors) {
                if !gc.is_zero() {
                    *acc = acc.add(&q.checked_mul(gc)?);
                }
            }
        }

        // 独立検算: `sum_i cofactors[i] * originals[i] + remainder == target`
        let mut recon = remainder.clone();
        for (h, f) in cofactors.iter().zip(&self.originals) {
            if !h.is_zero() && !f.is_zero() {
                recon = recon.add(&h.checked_mul(f)?);
            }
        }
        let verified = recon == *target;
        let is_member = remainder.is_zero() && verified;

        Ok(MembershipResult {
            is_member,
            remainder,
            cofactors,
            verified,
        })
    }

    /// `1 in I` の空性証明 witness を生成・検算する。
    pub fn empty_witness(&self) -> Result<Option<EmptyWitness>, AlgebraError> {
        let one = Poly::one(self.vars.len(), Rat::zero());
        let res = self.membership(&one)?;
        if !res.is_member {
            return Ok(None);
        }
        let generators = self
            .originals
            .iter()
            .map(|p| p.display(&self.vars, self.order))
            .collect();
        let cofactors = res
            .cofactors
            .iter()
            .map(|p| p.display(&self.vars, self.order))
            .collect();
        Ok(Some(EmptyWitness {
            generators,
            cofactors,
            verified: res.verified,
        }))
    }

    /// 基底による正規形（剰余のみ）を返す。
    pub fn normal_form(&self, target: &Poly<Rat>) -> Result<Poly<Rat>, AlgebraError> {
        if target.num_vars() != self.vars.len() {
            return Err(AlgebraError::ArityMismatch {
                expected: self.vars.len(),
                actual: target.num_vars(),
            });
        }
        let (rem, _) = divide_with_quotients(target, &self.basis, self.order)?;
        Ok(rem)
    }
}

/// Rabinowitsch 補助変数 `u_j` と式 `u_j * g_j - 1 = 0` を用いて
/// `V(equations) ∩ D(invertibles)` を計算し、補助変数を消去したパラメータ式と空性 witness を返す。
pub fn rabinowitsch_solve(
    equations: &[Poly<Rat>],
    invertibles: &[Poly<Rat>],
    vars: &VarOrder,
) -> Result<RabinowitschResult, AlgebraError> {
    let n = vars.len();
    for p in equations.iter().chain(invertibles) {
        if p.num_vars() != n {
            return Err(AlgebraError::ArityMismatch {
                expected: n,
                actual: p.num_vars(),
            });
        }
    }
    let m = invertibles.len();
    let aux_names: Vec<String> = (0..m).map(|i| fresh_aux_name(vars, i)).collect();
    let ext_vars = vars.prepend_vars(aux_names)?;
    let ext_n = ext_vars.len();

    let mut ext_gens: Vec<Poly<Rat>> = equations.iter().map(|p| p.lift_vars(m)).collect();
    let one = Poly::one(ext_n, Rat::zero());
    for (i, g) in invertibles.iter().enumerate() {
        let u_i = Poly::var(ext_n, i, Rat::zero());
        let g_ext = g.lift_vars(m);
        ext_gens.push(u_i.checked_mul(&g_ext)?.sub(&one));
    }

    // 補助変数を最上位に置いた Lex 順序により、補助変数を含まないパラメータ式が自然に消去される。
    let basis = GroebnerBasis::compute(&ext_gens, ext_vars.clone(), MonomialOrder::Lex)?;
    let is_empty = basis.contains_one();
    let empty_witness = if is_empty {
        basis.empty_witness()?
    } else {
        None
    };

    let mut parameter_equations = Vec::new();
    if !is_empty {
        for p in basis.basis_polys() {
            if let Some(projected) = p.drop_prefix_vars(m)
                && !projected.is_zero()
            {
                parameter_equations.push(projected);
            }
        }
    }

    Ok(RabinowitschResult {
        parameter_equations,
        is_empty_over_closure: is_empty,
        empty_witness,
        extended_vars: ext_vars,
        basis,
    })
}

fn fresh_aux_name(vars: &VarOrder, idx: usize) -> String {
    let mut candidate = format!("__u{idx}");
    while vars.index_of(&candidate).is_some() {
        candidate.push('_');
    }
    candidate
}

fn make_monic(mut tracked: TrackedPoly, order: MonomialOrder) -> TrackedPoly {
    let Some((_, lc)) = tracked.poly.leading_term(order) else {
        return tracked;
    };
    if lc.is_one() {
        return tracked;
    }
    let inv = lc.inv().expect("leading coefficient is nonzero");
    tracked.poly = tracked.poly.scale(&inv);
    for c in &mut tracked.cofactors {
        *c = c.scale(&inv);
    }
    tracked
}

fn s_polynomial(
    a: &TrackedPoly,
    b: &TrackedPoly,
    order: MonomialOrder,
) -> Result<TrackedPoly, AlgebraError> {
    let (lm_a, lc_a) = a
        .poly
        .leading_term(order)
        .expect("S-polynomial requires nonzero polynomials");
    let (lm_b, lc_b) = b
        .poly
        .leading_term(order)
        .expect("S-polynomial requires nonzero polynomials");
    let lcm = lm_a.lcm(lm_b);
    let m_a = lcm.div_exact(lm_a).expect("lcm divisible by lm_a");
    let m_b = lcm.div_exact(lm_b).expect("lcm divisible by lm_b");
    let inv_a = lc_a.inv().expect("lc_a nonzero");
    let inv_b = lc_b.inv().expect("lc_b nonzero");

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
    Ok(TrackedPoly { poly, cofactors })
}

fn reduce_tracked(
    target: &TrackedPoly,
    basis: &[TrackedPoly],
    order: MonomialOrder,
) -> Result<TrackedPoly, AlgebraError> {
    let n = target.poly.num_vars();
    let mut p = target.poly.clone();
    let mut cofactors = target.cofactors.clone();
    let mut rem = Poly::zero(n, Rat::zero());

    while let Some((lm_p, lc_p)) = p.leading_term(order) {
        let lm_p = lm_p.clone();
        let lc_p = lc_p.clone();
        let mut divided = false;
        for g in basis {
            if let Some((lm_g, lc_g)) = g.poly.leading_term(order)
                && let Some(q_mono) = lm_p.div_exact(lm_g)
            {
                let q_coeff = (&lc_p / lc_g).expect("divisor leading coeff nonzero");
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

    Ok(TrackedPoly {
        poly: rem,
        cofactors,
    })
}

fn divide_with_quotients(
    target: &Poly<Rat>,
    basis: &[TrackedPoly],
    order: MonomialOrder,
) -> Result<(Poly<Rat>, Vec<Poly<Rat>>), AlgebraError> {
    let n = target.num_vars();
    let mut p = target.clone();
    let mut rem = Poly::zero(n, Rat::zero());
    let mut quotients = vec![Poly::zero(n, Rat::zero()); basis.len()];

    while let Some((lm_p, lc_p)) = p.leading_term(order) {
        let lm_p = lm_p.clone();
        let lc_p = lc_p.clone();
        let mut divided = false;
        for (idx, g) in basis.iter().enumerate() {
            if let Some((lm_g, lc_g)) = g.poly.leading_term(order)
                && let Some(q_mono) = lm_p.div_exact(lm_g)
            {
                let q_coeff = (&lc_p / lc_g).expect("divisor leading coeff nonzero");
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

fn pop_min_degree_pair(pairs: &mut Vec<(usize, usize, u64)>) -> Option<(usize, usize)> {
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

fn chain_criterion_applies(
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
            let pair_ik = if i < k { (i, k) } else { (k, i) };
            let pair_jk = if j < k { (j, k) } else { (k, j) };
            if handled.contains(&pair_ik) && handled.contains(&pair_jk) {
                return true;
            }
        }
    }
    false
}

fn inter_reduce(
    basis: Vec<TrackedPoly>,
    order: MonomialOrder,
) -> Result<Vec<TrackedPoly>, AlgebraError> {
    let mut minimal: Vec<TrackedPoly> = Vec::new();
    for (i, candidate) in basis.iter().enumerate() {
        let Some((lm_i, _)) = candidate.poly.leading_term(order) else {
            continue;
        };
        let redundant = basis.iter().enumerate().any(|(j, other)| {
            if i == j {
                return false;
            }
            let Some((lm_j, _)) = other.poly.leading_term(order) else {
                return false;
            };
            lm_j.divides(lm_i) && (lm_j != lm_i || j < i)
        });
        if !redundant {
            minimal.push(make_monic(candidate.clone(), order));
        }
    }

    let mut reduced = minimal;
    for i in 0..reduced.len() {
        let others: Vec<TrackedPoly> = reduced
            .iter()
            .enumerate()
            .filter(|&(j, _)| j != i)
            .map(|(_, g)| g.clone())
            .collect();
        let next = make_monic(reduce_tracked(&reduced[i], &others, order)?, order);
        reduced[i] = next;
    }
    reduced.retain(|g| !g.poly.is_zero());
    reduced.sort_by(|a, b| {
        let ma = a.poly.leading_term(order).map(|(m, _)| m);
        let mb = b.poly.leading_term(order).map(|(m, _)| m);
        match (ma, mb) {
            (Some(x), Some(y)) => x.cmp_order(y, order),
            _ => std::cmp::Ordering::Equal,
        }
    });
    Ok(reduced)
}
