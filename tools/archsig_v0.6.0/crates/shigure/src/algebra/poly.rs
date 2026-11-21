//! 単項式・変数順序・多変数多項式 `Poly<C>` および `PolyExpr` からの展開変換。

use crate::algebra::MonomialOrder;
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::ir::term::{PolyExpr, ScalarLit};
use archsig_common::prime::is_prime;
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// 多項式環計算で発生し得るエラー。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlgebraError {
    /// 未観測値への依存が残るため多項式展開できない（沈黙へ接続）。
    UnobservedDependency { slots: Vec<String> },
    /// 環に未登録の変数を参照した。
    UnknownVariable { name: String },
    /// 係数域が計算環と一致しない。
    DomainMismatch { expected: String, actual: String },
    /// 素数でない法を指定した。
    InvalidPrimeModulus { modulus: BigUint },
    /// 変数数の不一致。
    ArityMismatch { expected: usize, actual: usize },
    /// 計算資源・ステップ上限超過または適用域外。
    OutOfScope { detail: String },
}

impl fmt::Display for AlgebraError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AlgebraError::UnobservedDependency { slots } => {
                write!(
                    f,
                    "expression depends on unobserved slots: {}",
                    slots.join(", ")
                )
            }
            AlgebraError::UnknownVariable { name } => write!(f, "unknown variable `{name}`"),
            AlgebraError::DomainMismatch { expected, actual } => {
                write!(
                    f,
                    "coefficient domain mismatch: expected {expected}, got {actual}"
                )
            }
            AlgebraError::InvalidPrimeModulus { modulus } => {
                write!(f, "modulus `{modulus}` is not prime")
            }
            AlgebraError::ArityMismatch { expected, actual } => {
                write!(f, "arity mismatch: expected {expected}, got {actual}")
            }
            AlgebraError::OutOfScope { detail } => write!(f, "out of scope: {detail}"),
        }
    }
}

impl std::error::Error for AlgebraError {}

/// 多項式環の変数順序（インデックス 0 が最上位変数）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VarOrder {
    vars: Vec<String>,
    index: BTreeMap<String, usize>,
}

impl VarOrder {
    pub fn new(vars: Vec<String>) -> Result<Self, AlgebraError> {
        let mut index = BTreeMap::new();
        for (i, v) in vars.iter().enumerate() {
            if v.trim().is_empty() || index.insert(v.clone(), i).is_some() {
                return Err(AlgebraError::OutOfScope {
                    detail: format!("invalid or duplicate variable name `{v}`"),
                });
            }
        }
        Ok(Self { vars, index })
    }

    pub fn len(&self) -> usize {
        self.vars.len()
    }

    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }

    pub fn vars(&self) -> &[String] {
        &self.vars
    }

    pub fn index_of(&self, name: &str) -> Option<usize> {
        self.index.get(name).copied()
    }

    /// 先頭に補助変数（Rabinowitsch 変数等）を追加した消去用の変数順序を返す。
    pub fn prepend_vars(&self, extra: Vec<String>) -> Result<Self, AlgebraError> {
        let mut combined = extra;
        combined.extend(self.vars.iter().cloned());
        Self::new(combined)
    }
}

/// `PolyExpr` の 3 名前空間（`StateVar` / `ArgVar` / `ParamVar`）を互いに分離して
/// 多項式環の変数インデックスへ対応付ける束縛表。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprBindings {
    num_vars: usize,
    state_vars: BTreeMap<String, usize>,
    arg_vars: BTreeMap<String, usize>,
    param_vars: BTreeMap<String, usize>,
}

impl ExprBindings {
    /// `VarOrder` の全変数を `ParamVar` 名前空間のみに束縛する（状態変数・引数変数は未束縛）。
    pub fn params_only(vars: &VarOrder) -> Self {
        let mut param_vars = BTreeMap::new();
        for (i, name) in vars.vars().iter().enumerate() {
            param_vars.insert(name.clone(), i);
        }
        Self {
            num_vars: vars.len(),
            state_vars: BTreeMap::new(),
            arg_vars: BTreeMap::new(),
            param_vars,
        }
    }

    /// 状態変数・引数変数・パラメータ変数の 3 名前空間を順に `[state..., arg..., param...]` へ配置し、
    /// 対応する `VarOrder` と `ExprBindings` を構築する。
    /// 異なる名前空間間で同名変数がある場合は表示名のみ接頭辞で分離し、名前空間自体は衝突させない。
    pub fn from_slices(
        state_names: &[String],
        arg_names: &[String],
        param_names: &[String],
    ) -> Result<(VarOrder, Self), AlgebraError> {
        for (kind, names) in [
            ("state", state_names),
            ("arg", arg_names),
            ("param", param_names),
        ] {
            let mut seen = BTreeSet::new();
            for name in names {
                if name.trim().is_empty() || !seen.insert(name.as_str()) {
                    return Err(AlgebraError::OutOfScope {
                        detail: format!("invalid or duplicate {kind} variable name `{name}`"),
                    });
                }
            }
        }

        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        for name in state_names
            .iter()
            .chain(arg_names.iter())
            .chain(param_names.iter())
        {
            *counts.entry(name.as_str()).or_insert(0) += 1;
        }

        let mut used_display: BTreeSet<String> = BTreeSet::new();
        let mut display_vars: Vec<String> =
            Vec::with_capacity(state_names.len() + arg_names.len() + param_names.len());
        let mut state_vars = BTreeMap::new();
        let mut arg_vars = BTreeMap::new();
        let mut param_vars = BTreeMap::new();

        let mut push_var = |prefix: &str, name: &str, map: &mut BTreeMap<String, usize>| {
            let idx = display_vars.len();
            let base = if counts.get(name).copied().unwrap_or(0) > 1 {
                format!("{prefix}::{name}")
            } else {
                name.to_owned()
            };
            let mut disp = base;
            while !used_display.insert(disp.clone()) {
                disp.push('_');
            }
            display_vars.push(disp);
            map.insert(name.to_owned(), idx);
        };

        for name in state_names {
            push_var("state", name, &mut state_vars);
        }
        for name in arg_names {
            push_var("arg", name, &mut arg_vars);
        }
        for name in param_names {
            push_var("param", name, &mut param_vars);
        }

        let order = VarOrder::new(display_vars)?;
        let bindings = Self {
            num_vars: order.len(),
            state_vars,
            arg_vars,
            param_vars,
        };
        Ok((order, bindings))
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    pub fn state_index(&self, name: &str) -> Option<usize> {
        self.state_vars.get(name).copied()
    }

    pub fn arg_index(&self, name: &str) -> Option<usize> {
        self.arg_vars.get(name).copied()
    }

    pub fn param_index(&self, name: &str) -> Option<usize> {
        self.param_vars.get(name).copied()
    }
}

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

fn expand_expr_with<C, F>(
    expr: &PolyExpr,
    bindings: &ExprBindings,
    zero: &C,
    lit_to_coeff: &F,
) -> Result<Poly<C>, AlgebraError>
where
    C: RingCoeff,
    F: Fn(&ScalarLit) -> Result<C, AlgebraError>,
{
    let n = bindings.num_vars();
    match expr {
        PolyExpr::Const(lit) => Ok(Poly::constant(n, lit_to_coeff(lit)?)),
        PolyExpr::StateVar(v) => {
            let idx = bindings
                .state_index(v)
                .ok_or_else(|| AlgebraError::UnknownVariable {
                    name: format!("state:{v}"),
                })?;
            Ok(Poly::var(n, idx, zero.clone()))
        }
        PolyExpr::ArgVar(v) => {
            let idx = bindings
                .arg_index(v)
                .ok_or_else(|| AlgebraError::UnknownVariable {
                    name: format!("arg:{v}"),
                })?;
            Ok(Poly::var(n, idx, zero.clone()))
        }
        PolyExpr::ParamVar(v) => {
            let idx = bindings
                .param_index(v)
                .ok_or_else(|| AlgebraError::UnknownVariable {
                    name: format!("param:{v}"),
                })?;
            Ok(Poly::var(n, idx, zero.clone()))
        }
        PolyExpr::Unobserved { slot, .. } => Err(AlgebraError::UnobservedDependency {
            slots: vec![slot.clone()],
        }),
        PolyExpr::Neg(e) => Ok(expand_expr_with(e, bindings, zero, lit_to_coeff)?.neg()),
        PolyExpr::Add(a, b) => Ok(expand_expr_with(a, bindings, zero, lit_to_coeff)?
            .add(&expand_expr_with(b, bindings, zero, lit_to_coeff)?)),
        PolyExpr::Sub(a, b) => Ok(expand_expr_with(a, bindings, zero, lit_to_coeff)?
            .sub(&expand_expr_with(b, bindings, zero, lit_to_coeff)?)),
        PolyExpr::Mul(a, b) => expand_expr_with(a, bindings, zero, lit_to_coeff)?
            .checked_mul(&expand_expr_with(b, bindings, zero, lit_to_coeff)?),
        PolyExpr::Pow(e, exp) => {
            expand_expr_with(e, bindings, zero, lit_to_coeff)?.checked_pow(*exp)
        }
    }
}

fn check_unobserved(expr: &PolyExpr) -> Result<(), AlgebraError> {
    let mut missing = BTreeSet::new();
    expr.collect_unobserved(&mut missing);
    if !missing.is_empty() {
        return Err(AlgebraError::UnobservedDependency {
            slots: missing.into_iter().collect(),
        });
    }
    Ok(())
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

    /// `PolyExpr` を `Q` 上の多項式へ展開する。未観測値を含む場合は零化せず `UnobservedDependency` を返す。
    pub fn from_expr_q(expr: &PolyExpr, bindings: &ExprBindings) -> Result<Self, AlgebraError> {
        check_unobserved(expr)?;
        let zero = Rat::zero();
        expand_expr_with(expr, bindings, &zero, &|lit| match lit {
            ScalarLit::Q { num, den } => {
                Rat::new(num.clone(), den.clone()).ok_or_else(|| AlgebraError::OutOfScope {
                    detail: "zero denominator in rational literal".to_owned(),
                })
            }
            ScalarLit::Z(z) => Ok(Rat::from_int(z.clone())),
            ScalarLit::Fp { modulus, .. } => Err(AlgebraError::DomainMismatch {
                expected: "Q".to_owned(),
                actual: format!("Fp({modulus})"),
            }),
        })
    }
}

impl Poly<BigInt> {
    /// `PolyExpr` を `Z` 上の多項式へ展開する。
    pub fn from_expr_z(expr: &PolyExpr, bindings: &ExprBindings) -> Result<Self, AlgebraError> {
        check_unobserved(expr)?;
        let zero = BigInt::zero();
        expand_expr_with(expr, bindings, &zero, &|lit| match lit {
            ScalarLit::Z(z) => Ok(z.clone()),
            other => Err(AlgebraError::DomainMismatch {
                expected: "Z".to_owned(),
                actual: other.domain().to_string(),
            }),
        })
    }
}

impl Poly<FpElem> {
    /// `PolyExpr` を素数体 `Fp(modulus)` 上の多項式へ展開する。
    pub fn from_expr_fp(
        expr: &PolyExpr,
        bindings: &ExprBindings,
        modulus: &BigUint,
    ) -> Result<Self, AlgebraError> {
        if !is_prime(modulus) {
            return Err(AlgebraError::InvalidPrimeModulus {
                modulus: modulus.clone(),
            });
        }
        check_unobserved(expr)?;
        let zero = FpElem::from_checked_prime(BigInt::zero(), modulus.clone());
        expand_expr_with(expr, bindings, &zero, &|lit| match lit {
            ScalarLit::Fp {
                value,
                modulus: lit_mod,
            } => {
                if lit_mod != modulus {
                    return Err(AlgebraError::DomainMismatch {
                        expected: format!("Fp({modulus})"),
                        actual: format!("Fp({lit_mod})"),
                    });
                }
                Ok(FpElem::from_checked_prime(
                    BigInt::from(value.clone()),
                    modulus.clone(),
                ))
            }
            other => Err(AlgebraError::DomainMismatch {
                expected: format!("Fp({modulus})"),
                actual: other.domain().to_string(),
            }),
        })
    }
}
