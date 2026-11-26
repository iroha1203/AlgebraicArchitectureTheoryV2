//! 単項式 `Monomial`・多変数多項式 `Poly<C>`（偏微分・多項式代入・次数打ち切り含む）。

use crate::algebra::MonomialOrder;
use crate::algebra::scalar::{Rat, RingCoeff};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

pub use crate::algebra::poly_expr::{AlgebraError, ExprBindings, VarOrder};

/// 固定変数数上の単項式（指数ベクトル）。
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Monomial {
    exps: Vec<u32>,
}

impl Monomial {
    pub fn one(num_vars: usize) -> Self {
        Self {
            exps: vec![0; num_vars],
        }
    }

    pub fn var(num_vars: usize, idx: usize) -> Self {
        let mut exps = vec![0; num_vars];
        exps[idx] = 1;
        Self { exps }
    }

    pub fn from_exps(exps: Vec<u32>) -> Self {
        Self { exps }
    }

    pub fn exps(&self) -> &[u32] {
        &self.exps
    }

    pub fn num_vars(&self) -> usize {
        self.exps.len()
    }

    pub fn total_degree(&self) -> u64 {
        self.exps.iter().map(|&e| u64::from(e)).sum()
    }

    pub fn is_one(&self) -> bool {
        self.exps.iter().all(|&e| e == 0)
    }

    /// 指数 > 0 の変数インデックス集合（G-141 F11–F12 の支持）。
    pub fn support(&self) -> BTreeSet<usize> {
        self.exps
            .iter()
            .enumerate()
            .filter_map(|(i, &e)| (e > 0).then_some(i))
            .collect()
    }

    pub fn checked_mul(&self, other: &Self) -> Option<Self> {
        assert_eq!(self.exps.len(), other.exps.len(), "monomial arity mismatch");
        let mut exps = Vec::with_capacity(self.exps.len());
        for (&a, &b) in self.exps.iter().zip(&other.exps) {
            exps.push(a.checked_add(b)?);
        }
        Some(Self { exps })
    }

    pub fn mul(&self, other: &Self) -> Self {
        self.checked_mul(other)
            .expect("monomial exponent addition overflowed u32")
    }

    pub fn divides(&self, target: &Self) -> bool {
        assert_eq!(
            self.exps.len(),
            target.exps.len(),
            "monomial arity mismatch"
        );
        self.exps.iter().zip(&target.exps).all(|(&a, &b)| a <= b)
    }

    pub fn div_exact(&self, divisor: &Self) -> Option<Self> {
        if !divisor.divides(self) {
            return None;
        }
        let exps = self
            .exps
            .iter()
            .zip(&divisor.exps)
            .map(|(&a, &b)| a - b)
            .collect();
        Some(Self { exps })
    }

    pub fn lcm(&self, other: &Self) -> Self {
        assert_eq!(self.exps.len(), other.exps.len(), "monomial arity mismatch");
        let exps = self
            .exps
            .iter()
            .zip(&other.exps)
            .map(|(&a, &b)| a.max(b))
            .collect();
        Self { exps }
    }

    /// Buchberger 第 1 基準（互いに素判定: `gcd(m1, m2) == 1`）。
    pub fn gcd_is_one(&self, other: &Self) -> bool {
        assert_eq!(self.exps.len(), other.exps.len(), "monomial arity mismatch");
        self.exps
            .iter()
            .zip(&other.exps)
            .all(|(&a, &b)| a == 0 || b == 0)
    }

    pub fn cmp_order(&self, other: &Self, order: MonomialOrder) -> Ordering {
        assert_eq!(self.exps.len(), other.exps.len(), "monomial arity mismatch");
        match order {
            MonomialOrder::Lex => self.exps.cmp(&other.exps),
            MonomialOrder::Grevlex => {
                let d1 = self.total_degree();
                let d2 = other.total_degree();
                match d1.cmp(&d2) {
                    Ordering::Equal => {
                        for (&a, &b) in self.exps.iter().rev().zip(other.exps.iter().rev()) {
                            if a != b {
                                // Grevlex: 末尾の指数が小さい方が大きい単項式。
                                return b.cmp(&a);
                            }
                        }
                        Ordering::Equal
                    }
                    ord => ord,
                }
            }
        }
    }

    pub fn display(&self, vars: &VarOrder) -> String {
        let mut parts = Vec::new();
        for (i, &e) in self.exps.iter().enumerate() {
            if e == 1 {
                parts.push(vars.vars()[i].clone());
            } else if e > 1 {
                parts.push(format!("{}^{e}", vars.vars()[i]));
            }
        }
        if parts.is_empty() {
            "1".to_owned()
        } else {
            parts.join("*")
        }
    }
}

impl Ord for Monomial {
    fn cmp(&self, other: &Self) -> Ordering {
        self.exps.cmp(&other.exps)
    }
}

impl PartialOrd for Monomial {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// 疎表現の多変数多項式（非零係数のみを保持する正規表現）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Poly<C: RingCoeff> {
    num_vars: usize,
    zero_coeff: C,
    terms: BTreeMap<Monomial, C>,
}

impl<C: RingCoeff> Poly<C> {
    pub fn zero(num_vars: usize, zero_coeff: C) -> Self {
        Self {
            num_vars,
            zero_coeff: zero_coeff.zero_like(),
            terms: BTreeMap::new(),
        }
    }

    pub fn constant(num_vars: usize, coeff: C) -> Self {
        let zero_coeff = coeff.zero_like();
        let mut terms = BTreeMap::new();
        if !coeff.coeff_is_zero() {
            terms.insert(Monomial::one(num_vars), coeff);
        }
        Self {
            num_vars,
            zero_coeff,
            terms,
        }
    }

    pub fn one(num_vars: usize, zero_coeff: C) -> Self {
        let one = zero_coeff.one_like();
        Self::constant(num_vars, one)
    }

    pub fn var(num_vars: usize, idx: usize, zero_coeff: C) -> Self {
        let zero_coeff = zero_coeff.zero_like();
        let one = zero_coeff.one_like();
        let mut terms = BTreeMap::new();
        if !one.coeff_is_zero() {
            terms.insert(Monomial::var(num_vars, idx), one);
        }
        Self {
            num_vars,
            zero_coeff,
            terms,
        }
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    pub fn zero_coeff(&self) -> &C {
        &self.zero_coeff
    }

    pub fn terms(&self) -> &BTreeMap<Monomial, C> {
        &self.terms
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn is_constant(&self) -> bool {
        self.terms.is_empty()
            || (self.terms.len() == 1 && self.terms.keys().next().is_some_and(Monomial::is_one))
    }

    pub fn constant_value(&self) -> C {
        self.terms
            .get(&Monomial::one(self.num_vars))
            .cloned()
            .unwrap_or_else(|| self.zero_coeff.clone())
    }

    pub fn total_degree(&self) -> u64 {
        self.terms
            .keys()
            .map(Monomial::total_degree)
            .max()
            .unwrap_or(0)
    }

    pub fn is_affine(&self) -> bool {
        self.total_degree() <= 1
    }

    fn check_arity(&self, actual: usize) -> Result<(), AlgebraError> {
        if actual != self.num_vars {
            return Err(AlgebraError::ArityMismatch {
                expected: self.num_vars,
                actual,
            });
        }
        Ok(())
    }

    fn check_ring(&self, coeff: &C) -> Result<(), AlgebraError> {
        if !self.zero_coeff.same_ring(coeff) {
            return Err(AlgebraError::DomainMismatch {
                expected: format!("{:?}", self.zero_coeff),
                actual: format!("{coeff:?}"),
            });
        }
        Ok(())
    }

    /// 変数数・係数環（`FpElem` の法を含む）を検査した上で単項式項を加算する。
    pub fn try_add_term(&mut self, mono: Monomial, coeff: C) -> Result<(), AlgebraError> {
        self.check_arity(mono.num_vars())?;
        self.check_ring(&coeff)?;
        if coeff.coeff_is_zero() {
            return Ok(());
        }
        let next = match self.terms.get(&mono) {
            Some(existing) => existing.add_ref(&coeff),
            None => coeff,
        };
        if next.coeff_is_zero() {
            self.terms.remove(&mono);
        } else {
            self.terms.insert(mono, next);
        }
        Ok(())
    }

    pub fn add_term(&mut self, mono: Monomial, coeff: C) {
        self.try_add_term(mono, coeff)
            .expect("polynomial arity or coefficient ring mismatch");
    }

    pub fn remove_term(&mut self, mono: &Monomial) -> Option<C> {
        assert_eq!(mono.num_vars(), self.num_vars, "polynomial arity mismatch");
        self.terms.remove(mono)
    }

    /// 変数数・係数環・単項式指数のオーバーフローを検査しながら
    /// `self -= other * (scalar * mono)` を in-place 実行する（失敗時は `self` を破壊しない）。
    pub fn checked_sub_mul_term_assign(
        &mut self,
        other: &Self,
        mono: &Monomial,
        scalar: &C,
    ) -> Result<(), AlgebraError> {
        self.check_arity(other.num_vars)?;
        self.check_arity(mono.num_vars())?;
        self.check_ring(&other.zero_coeff)?;
        self.check_ring(scalar)?;
        if scalar.coeff_is_zero() || other.is_zero() {
            return Ok(());
        }
        let mut updates = Vec::with_capacity(other.terms.len());
        for (m, c) in &other.terms {
            let prod = c.mul_ref(scalar).neg_ref();
            if !prod.coeff_is_zero() {
                let shifted = m
                    .checked_mul(mono)
                    .ok_or_else(|| AlgebraError::OutOfScope {
                        detail: "monomial exponent addition overflowed u32".to_owned(),
                    })?;
                updates.push((shifted, prod));
            }
        }
        for (shifted, prod) in updates {
            self.add_term(shifted, prod);
        }
        Ok(())
    }

    /// `self -= other * (scalar * mono)` を多項式全体の複製なしに in-place 実行する。
    pub fn sub_mul_term_assign(&mut self, other: &Self, mono: &Monomial, scalar: &C) {
        self.checked_sub_mul_term_assign(other, mono, scalar)
            .expect("polynomial arity, ring, or exponent overflow in sub_mul_term_assign");
    }

    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(self.num_vars, other.num_vars, "polynomial arity mismatch");
        assert!(
            self.zero_coeff.same_ring(&other.zero_coeff),
            "polynomial coefficient ring mismatch"
        );
        let mut out = self.clone();
        for (m, c) in &other.terms {
            out.add_term(m.clone(), c.clone());
        }
        out
    }

    pub fn neg(&self) -> Self {
        let terms = self
            .terms
            .iter()
            .map(|(m, c)| (m.clone(), c.neg_ref()))
            .collect();
        Self {
            num_vars: self.num_vars,
            zero_coeff: self.zero_coeff.clone(),
            terms,
        }
    }

    pub fn sub(&self, other: &Self) -> Self {
        assert_eq!(self.num_vars, other.num_vars, "polynomial arity mismatch");
        assert!(
            self.zero_coeff.same_ring(&other.zero_coeff),
            "polynomial coefficient ring mismatch"
        );
        let mut out = self.clone();
        for (m, c) in &other.terms {
            out.add_term(m.clone(), c.neg_ref());
        }
        out
    }

    pub fn scale(&self, scalar: &C) -> Self {
        assert!(
            self.zero_coeff.same_ring(scalar),
            "polynomial scalar ring mismatch"
        );
        if scalar.coeff_is_zero() || self.is_zero() {
            return Self::zero(self.num_vars, self.zero_coeff.clone());
        }
        let mut out = Self::zero(self.num_vars, self.zero_coeff.clone());
        for (m, c) in &self.terms {
            let prod = c.mul_ref(scalar);
            if !prod.coeff_is_zero() {
                out.terms.insert(m.clone(), prod);
            }
        }
        out
    }

    /// 変数数・係数環・単項式指数のオーバーフローを検査しながら単項式項を掛ける。
    pub fn checked_mul_term(&self, mono: &Monomial, scalar: &C) -> Result<Self, AlgebraError> {
        self.check_arity(mono.num_vars())?;
        self.check_ring(scalar)?;
        if scalar.coeff_is_zero() || self.is_zero() {
            return Ok(Self::zero(self.num_vars, self.zero_coeff.clone()));
        }
        let mut out = Self::zero(self.num_vars, self.zero_coeff.clone());
        for (m, c) in &self.terms {
            let prod = c.mul_ref(scalar);
            if !prod.coeff_is_zero() {
                let shifted = m
                    .checked_mul(mono)
                    .ok_or_else(|| AlgebraError::OutOfScope {
                        detail: "monomial exponent addition overflowed u32".to_owned(),
                    })?;
                out.add_term(shifted, prod);
            }
        }
        Ok(out)
    }

    pub fn mul_term(&self, mono: &Monomial, scalar: &C) -> Self {
        self.checked_mul_term(mono, scalar)
            .expect("polynomial arity, ring, or exponent overflow in mul_term")
    }

    /// 変数数・係数環・単項式指数のオーバーフローを検査しながら乗算する。
    pub fn checked_mul(&self, other: &Self) -> Result<Self, AlgebraError> {
        self.check_arity(other.num_vars)?;
        self.check_ring(&other.zero_coeff)?;
        if self.is_zero() || other.is_zero() {
            return Ok(Self::zero(self.num_vars, self.zero_coeff.clone()));
        }
        let mut out = Self::zero(self.num_vars, self.zero_coeff.clone());
        for (m1, c1) in &self.terms {
            for (m2, c2) in &other.terms {
                let mono = m1.checked_mul(m2).ok_or_else(|| AlgebraError::OutOfScope {
                    detail: "monomial exponent addition overflowed u32".to_owned(),
                })?;
                out.add_term(mono, c1.mul_ref(c2));
            }
        }
        Ok(out)
    }

    pub fn mul(&self, other: &Self) -> Self {
        self.checked_mul(other)
            .expect("polynomial arity, ring, or exponent overflow in mul")
    }

    /// 単項式指数のオーバーフローを検査しながら冪乗する。
    pub fn checked_pow(&self, mut exp: u32) -> Result<Self, AlgebraError> {
        if exp == 0 {
            return Ok(Self::one(self.num_vars, self.zero_coeff.clone()));
        }
        if self.is_zero() {
            return Ok(Self::zero(self.num_vars, self.zero_coeff.clone()));
        }
        let mut result = Self::one(self.num_vars, self.zero_coeff.clone());
        let mut base = self.clone();
        while exp > 0 {
            if exp % 2 == 1 {
                result = result.checked_mul(&base)?;
            }
            exp /= 2;
            if exp > 0 {
                base = base.checked_mul(&base)?;
            }
        }
        Ok(result)
    }

    pub fn pow(&self, exp: u32) -> Self {
        self.checked_pow(exp)
            .expect("monomial exponent overflow in pow")
    }

    /// 形式偏微分 `∂self / ∂x_{var_idx}`（標数 p でも正確に `e * 1` を計算）。
    pub fn partial_derivative(&self, var_idx: usize) -> Result<Self, AlgebraError> {
        if var_idx >= self.num_vars {
            return Err(AlgebraError::ArityMismatch {
                expected: self.num_vars,
                actual: var_idx + 1,
            });
        }
        let mut out = Self::zero(self.num_vars, self.zero_coeff.clone());
        for (mono, coeff) in &self.terms {
            let exp = mono.exps()[var_idx];
            if exp == 0 {
                continue;
            }
            let factor = self.zero_coeff.u32_like(exp);
            let next_coeff = coeff.mul_ref(&factor);
            if next_coeff.coeff_is_zero() {
                continue;
            }
            let mut next_exps = mono.exps().to_vec();
            next_exps[var_idx] = exp - 1;
            out.add_term(Monomial::from_exps(next_exps), next_coeff);
        }
        Ok(out)
    }

    /// 各変数 `x_i` へ多項式 `replacements[i]` を同時代入する（出力変数数は `replacements` の変数数）。
    pub fn substitute(&self, replacements: &[Self]) -> Result<Self, AlgebraError> {
        self.check_arity(replacements.len())?;
        let out_vars = replacements.first().map_or(self.num_vars, |p| p.num_vars());
        for p in replacements {
            if p.num_vars() != out_vars {
                return Err(AlgebraError::ArityMismatch {
                    expected: out_vars,
                    actual: p.num_vars(),
                });
            }
            self.check_ring(&p.zero_coeff)?;
        }
        let mut acc = Self::zero(out_vars, self.zero_coeff.clone());
        for (mono, coeff) in &self.terms {
            let mut term = Self::constant(out_vars, coeff.clone());
            for (idx, &e) in mono.exps().iter().enumerate() {
                if e > 0 {
                    let powered = replacements[idx].checked_pow(e)?;
                    term = term.checked_mul(&powered)?;
                }
            }
            acc = acc.add(&term);
        }
        Ok(acc)
    }

    /// 全次数が `max_deg` 以下の項だけを残した打ち切り多項式（`mod m^{max_deg + 1}`）を返す。
    pub fn truncate_degree(&self, max_deg: u64) -> Self {
        let mut out = Self::zero(self.num_vars, self.zero_coeff.clone());
        for (mono, coeff) in &self.terms {
            if mono.total_degree() <= max_deg {
                out.terms.insert(mono.clone(), coeff.clone());
            }
        }
        out
    }

    pub fn leading_term(&self, order: MonomialOrder) -> Option<(&Monomial, &C)> {
        self.terms
            .iter()
            .max_by(|(m1, _), (m2, _)| m1.cmp_order(m2, order))
    }

    /// 変数へのスカラー代入による評価。
    pub fn eval_at(&self, values: &[C]) -> Result<C, AlgebraError> {
        self.check_arity(values.len())?;
        for v in values {
            self.check_ring(v)?;
        }
        let mut acc = self.zero_coeff.clone();
        for (mono, coeff) in &self.terms {
            let mut term_val = coeff.clone();
            for (idx, &e) in mono.exps().iter().enumerate() {
                if e > 0 {
                    let p = pow_coeff(&values[idx], e, self.zero_coeff.one_like());
                    term_val = term_val.mul_ref(&p);
                }
            }
            acc = acc.add_ref(&term_val);
        }
        Ok(acc)
    }

    /// 一部の変数へスカラー値を固定代入し、同じ環上の多項式として縮約する。
    pub fn partial_eval(&self, fixed: &BTreeMap<usize, C>) -> Self {
        for (&idx, val) in fixed {
            assert!(
                idx < self.num_vars,
                "partial_eval variable index {idx} out of bounds (num_vars = {})",
                self.num_vars
            );
            assert!(
                self.zero_coeff.same_ring(val),
                "partial_eval coefficient ring mismatch"
            );
        }
        let mut out = Self::zero(self.num_vars, self.zero_coeff.clone());
        for (mono, coeff) in &self.terms {
            let mut new_exps = mono.exps().to_vec();
            let mut new_coeff = coeff.clone();
            for (&idx, val) in fixed {
                if new_exps[idx] > 0 {
                    let e = new_exps[idx];
                    new_exps[idx] = 0;
                    let p = pow_coeff(val, e, self.zero_coeff.one_like());
                    new_coeff = new_coeff.mul_ref(&p);
                }
            }
            out.add_term(Monomial::from_exps(new_exps), new_coeff);
        }
        out
    }

    /// 変数空間の埋め込み（先頭に `prepend` 個の補助変数を追加する等）。
    pub fn lift_vars(&self, prepend: usize) -> Self {
        let mut terms = BTreeMap::new();
        for (mono, coeff) in &self.terms {
            let mut exps = vec![0; prepend];
            exps.extend_from_slice(mono.exps());
            terms.insert(Monomial::from_exps(exps), coeff.clone());
        }
        Self {
            num_vars: self.num_vars + prepend,
            zero_coeff: self.zero_coeff.clone(),
            terms,
        }
    }

    /// 先頭 `drop_prefix` 個の補助変数が一切現れない場合のみ元の環へ射影する。
    pub fn drop_prefix_vars(&self, drop_prefix: usize) -> Option<Self> {
        if drop_prefix > self.num_vars {
            return None;
        }
        let mut terms = BTreeMap::new();
        for (mono, coeff) in &self.terms {
            if mono.exps()[..drop_prefix].iter().any(|&e| e > 0) {
                return None;
            }
            terms.insert(
                Monomial::from_exps(mono.exps()[drop_prefix..].to_vec()),
                coeff.clone(),
            );
        }
        Some(Self {
            num_vars: self.num_vars - drop_prefix,
            zero_coeff: self.zero_coeff.clone(),
            terms,
        })
    }

    pub fn display(&self, vars: &VarOrder, order: MonomialOrder) -> String {
        if self.is_zero() {
            return "0".to_owned();
        }
        let mut items: Vec<(&Monomial, &C)> = self.terms.iter().collect();
        items.sort_by(|(m1, _), (m2, _)| m2.cmp_order(m1, order));
        let mut out = String::new();
        for (i, (mono, coeff)) in items.into_iter().enumerate() {
            let c_str = coeff.to_string();
            let neg = c_str.starts_with('-');
            let abs_str = c_str.strip_prefix('-').unwrap_or(&c_str);
            if i == 0 {
                if neg {
                    out.push('-');
                }
            } else if neg {
                out.push_str(" - ");
            } else {
                out.push_str(" + ");
            }
            if mono.is_one() {
                out.push_str(abs_str);
            } else if abs_str == "1" {
                out.push_str(&mono.display(vars));
            } else {
                out.push_str(abs_str);
                out.push('*');
                out.push_str(&mono.display(vars));
            }
        }
        out
    }
}

fn pow_coeff<C: RingCoeff>(base: &C, mut exp: u32, one: C) -> C {
    let mut acc = one;
    let mut b = base.clone();
    while exp > 0 {
        if exp % 2 == 1 {
            acc = acc.mul_ref(&b);
        }
        exp /= 2;
        if exp > 0 {
            b = b.mul_ref(&b);
        }
    }
    acc
}

impl Poly<Rat> {
    pub fn monic(&self, order: MonomialOrder) -> Self {
        let Some((_, lc)) = self.leading_term(order) else {
            return self.clone();
        };
        let inv = lc
            .inv()
            .expect("leading coefficient of nonzero polynomial is nonzero");
        self.scale(&inv)
    }
}
