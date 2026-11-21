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

    pub fn total_degree(&self) -> u32 {
        self.exps.iter().copied().fold(0u32, u32::saturating_add)
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

    pub fn mul(&self, other: &Self) -> Self {
        debug_assert_eq!(self.exps.len(), other.exps.len());
        let exps = self
            .exps
            .iter()
            .zip(&other.exps)
            .map(|(&a, &b)| a.saturating_add(b))
            .collect();
        Self { exps }
    }

    pub fn divides(&self, target: &Self) -> bool {
        debug_assert_eq!(self.exps.len(), target.exps.len());
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
        debug_assert_eq!(self.exps.len(), other.exps.len());
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
        debug_assert_eq!(self.exps.len(), other.exps.len());
        self.exps
            .iter()
            .zip(&other.exps)
            .all(|(&a, &b)| a == 0 || b == 0)
    }

    pub fn cmp_order(&self, other: &Self, order: MonomialOrder) -> Ordering {
        debug_assert_eq!(self.exps.len(), other.exps.len());
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
            zero_coeff,
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

    pub fn total_degree(&self) -> u32 {
        self.terms
            .keys()
            .map(Monomial::total_degree)
            .max()
            .unwrap_or(0)
    }

    pub fn is_affine(&self) -> bool {
        self.total_degree() <= 1
    }

    pub fn add_term(&mut self, mono: Monomial, coeff: C) {
        debug_assert_eq!(mono.num_vars(), self.num_vars);
        if coeff.coeff_is_zero() {
            return;
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
    }

    pub fn add(&self, other: &Self) -> Self {
        debug_assert_eq!(self.num_vars, other.num_vars);
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
        debug_assert_eq!(self.num_vars, other.num_vars);
        let mut out = self.clone();
        for (m, c) in &other.terms {
            out.add_term(m.clone(), c.neg_ref());
        }
        out
    }

    pub fn scale(&self, scalar: &C) -> Self {
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

    pub fn mul_term(&self, mono: &Monomial, scalar: &C) -> Self {
        if scalar.coeff_is_zero() || self.is_zero() {
            return Self::zero(self.num_vars, self.zero_coeff.clone());
        }
        let mut out = Self::zero(self.num_vars, self.zero_coeff.clone());
        for (m, c) in &self.terms {
            let prod = c.mul_ref(scalar);
            if !prod.coeff_is_zero() {
                out.terms.insert(m.mul(mono), prod);
            }
        }
        out
    }

    pub fn mul(&self, other: &Self) -> Self {
        debug_assert_eq!(self.num_vars, other.num_vars);
        if self.is_zero() || other.is_zero() {
            return Self::zero(self.num_vars, self.zero_coeff.clone());
        }
        let mut out = Self::zero(self.num_vars, self.zero_coeff.clone());
        for (m1, c1) in &self.terms {
            for (m2, c2) in &other.terms {
                out.add_term(m1.mul(m2), c1.mul_ref(c2));
            }
        }
        out
    }

    pub fn pow(&self, mut exp: u32) -> Self {
        let mut result = Self::one(self.num_vars, self.zero_coeff.clone());
        let mut base = self.clone();
        while exp > 0 {
            if exp % 2 == 1 {
                result = result.mul(&base);
            }
            exp /= 2;
            if exp > 0 {
                base = base.mul(&base);
            }
        }
        result
    }

    pub fn leading_term(&self, order: MonomialOrder) -> Option<(&Monomial, &C)> {
        self.terms
            .iter()
            .max_by(|(m1, _), (m2, _)| m1.cmp_order(m2, order))
    }

    /// 変数へのスカラー代入による評価。
    pub fn eval_at(&self, values: &[C]) -> Result<C, AlgebraError> {
        if values.len() != self.num_vars {
            return Err(AlgebraError::ArityMismatch {
                expected: self.num_vars,
                actual: values.len(),
            });
        }
        let mut acc = self.zero_coeff.clone();
        for (mono, coeff) in &self.terms {
            let mut term_val = coeff.clone();
            for (idx, &e) in mono.exps().iter().enumerate() {
                if e > 0 {
                    let mut p = self.zero_coeff.one_like();
                    let mut b = values[idx].clone();
                    let mut k = e;
                    while k > 0 {
                        if k % 2 == 1 {
                            p = p.mul_ref(&b);
                        }
                        k /= 2;
                        if k > 0 {
                            b = b.mul_ref(&b);
                        }
                    }
                    term_val = term_val.mul_ref(&p);
                }
            }
            acc = acc.add_ref(&term_val);
        }
        Ok(acc)
    }

    /// 一部の変数へスカラー値を固定代入し、同じ環上の多項式として縮約する。
    pub fn partial_eval(&self, fixed: &BTreeMap<usize, C>) -> Self {
        let mut out = Self::zero(self.num_vars, self.zero_coeff.clone());
        for (mono, coeff) in &self.terms {
            let mut new_exps = mono.exps().to_vec();
            let mut new_coeff = coeff.clone();
            for (&idx, val) in fixed {
                if idx < self.num_vars && new_exps[idx] > 0 {
                    let e = new_exps[idx];
                    new_exps[idx] = 0;
                    for _ in 0..e {
                        new_coeff = new_coeff.mul_ref(val);
                    }
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
    pub fn from_expr_q(expr: &PolyExpr, vars: &VarOrder) -> Result<Self, AlgebraError> {
        let mut missing = BTreeSet::new();
        expr.collect_unobserved(&mut missing);
        if !missing.is_empty() {
            return Err(AlgebraError::UnobservedDependency {
                slots: missing.into_iter().collect(),
            });
        }
        expand_expr_q(expr, vars)
    }
}

fn expand_expr_q(expr: &PolyExpr, vars: &VarOrder) -> Result<Poly<Rat>, AlgebraError> {
    let n = vars.len();
    match expr {
        PolyExpr::Const(ScalarLit::Q { num, den }) => {
            let rat =
                Rat::new(num.clone(), den.clone()).ok_or_else(|| AlgebraError::OutOfScope {
                    detail: "zero denominator in rational literal".to_owned(),
                })?;
            Ok(Poly::constant(n, rat))
        }
        PolyExpr::Const(ScalarLit::Z(z)) => Ok(Poly::constant(n, Rat::from_int(z.clone()))),
        PolyExpr::Const(ScalarLit::Fp { modulus, .. }) => Err(AlgebraError::DomainMismatch {
            expected: "Q".to_owned(),
            actual: format!("Fp({modulus})"),
        }),
        PolyExpr::StateVar(v) | PolyExpr::ArgVar(v) | PolyExpr::ParamVar(v) => {
            let idx = vars
                .index_of(v)
                .ok_or_else(|| AlgebraError::UnknownVariable { name: v.clone() })?;
            Ok(Poly::var(n, idx, Rat::zero()))
        }
        PolyExpr::Unobserved { slot, .. } => Err(AlgebraError::UnobservedDependency {
            slots: vec![slot.clone()],
        }),
        PolyExpr::Neg(e) => Ok(expand_expr_q(e, vars)?.neg()),
        PolyExpr::Add(a, b) => Ok(expand_expr_q(a, vars)?.add(&expand_expr_q(b, vars)?)),
        PolyExpr::Sub(a, b) => Ok(expand_expr_q(a, vars)?.sub(&expand_expr_q(b, vars)?)),
        PolyExpr::Mul(a, b) => Ok(expand_expr_q(a, vars)?.mul(&expand_expr_q(b, vars)?)),
        PolyExpr::Pow(e, exp) => Ok(expand_expr_q(e, vars)?.pow(*exp)),
    }
}

impl Poly<BigInt> {
    /// `PolyExpr` を `Z` 上の多項式へ展開する。
    pub fn from_expr_z(expr: &PolyExpr, vars: &VarOrder) -> Result<Self, AlgebraError> {
        let mut missing = BTreeSet::new();
        expr.collect_unobserved(&mut missing);
        if !missing.is_empty() {
            return Err(AlgebraError::UnobservedDependency {
                slots: missing.into_iter().collect(),
            });
        }
        expand_expr_z(expr, vars)
    }
}

fn expand_expr_z(expr: &PolyExpr, vars: &VarOrder) -> Result<Poly<BigInt>, AlgebraError> {
    let n = vars.len();
    match expr {
        PolyExpr::Const(ScalarLit::Z(z)) => Ok(Poly::constant(n, z.clone())),
        PolyExpr::Const(other) => Err(AlgebraError::DomainMismatch {
            expected: "Z".to_owned(),
            actual: other.domain().to_string(),
        }),
        PolyExpr::StateVar(v) | PolyExpr::ArgVar(v) | PolyExpr::ParamVar(v) => {
            let idx = vars
                .index_of(v)
                .ok_or_else(|| AlgebraError::UnknownVariable { name: v.clone() })?;
            Ok(Poly::var(n, idx, BigInt::zero()))
        }
        PolyExpr::Unobserved { slot, .. } => Err(AlgebraError::UnobservedDependency {
            slots: vec![slot.clone()],
        }),
        PolyExpr::Neg(e) => Ok(expand_expr_z(e, vars)?.neg()),
        PolyExpr::Add(a, b) => Ok(expand_expr_z(a, vars)?.add(&expand_expr_z(b, vars)?)),
        PolyExpr::Sub(a, b) => Ok(expand_expr_z(a, vars)?.sub(&expand_expr_z(b, vars)?)),
        PolyExpr::Mul(a, b) => Ok(expand_expr_z(a, vars)?.mul(&expand_expr_z(b, vars)?)),
        PolyExpr::Pow(e, exp) => Ok(expand_expr_z(e, vars)?.pow(*exp)),
    }
}

impl Poly<FpElem> {
    /// `PolyExpr` を素数体 `Fp(modulus)` 上の多項式へ展開する。
    pub fn from_expr_fp(
        expr: &PolyExpr,
        vars: &VarOrder,
        modulus: &BigUint,
    ) -> Result<Self, AlgebraError> {
        if !is_prime(modulus) {
            return Err(AlgebraError::InvalidPrimeModulus {
                modulus: modulus.clone(),
            });
        }
        let mut missing = BTreeSet::new();
        expr.collect_unobserved(&mut missing);
        if !missing.is_empty() {
            return Err(AlgebraError::UnobservedDependency {
                slots: missing.into_iter().collect(),
            });
        }
        expand_expr_fp(expr, vars, modulus)
    }
}

fn expand_expr_fp(
    expr: &PolyExpr,
    vars: &VarOrder,
    modulus: &BigUint,
) -> Result<Poly<FpElem>, AlgebraError> {
    let n = vars.len();
    let zero = FpElem::from_checked_prime(BigInt::zero(), modulus.clone());
    match expr {
        PolyExpr::Const(ScalarLit::Fp {
            value,
            modulus: lit_mod,
        }) => {
            if lit_mod != modulus {
                return Err(AlgebraError::DomainMismatch {
                    expected: format!("Fp({modulus})"),
                    actual: format!("Fp({lit_mod})"),
                });
            }
            let elem = FpElem::from_checked_prime(BigInt::from(value.clone()), modulus.clone());
            Ok(Poly::constant(n, elem))
        }
        PolyExpr::Const(other) => Err(AlgebraError::DomainMismatch {
            expected: format!("Fp({modulus})"),
            actual: other.domain().to_string(),
        }),
        PolyExpr::StateVar(v) | PolyExpr::ArgVar(v) | PolyExpr::ParamVar(v) => {
            let idx = vars
                .index_of(v)
                .ok_or_else(|| AlgebraError::UnknownVariable { name: v.clone() })?;
            Ok(Poly::var(n, idx, zero))
        }
        PolyExpr::Unobserved { slot, .. } => Err(AlgebraError::UnobservedDependency {
            slots: vec![slot.clone()],
        }),
        PolyExpr::Neg(e) => Ok(expand_expr_fp(e, vars, modulus)?.neg()),
        PolyExpr::Add(a, b) => {
            Ok(expand_expr_fp(a, vars, modulus)?.add(&expand_expr_fp(b, vars, modulus)?))
        }
        PolyExpr::Sub(a, b) => {
            Ok(expand_expr_fp(a, vars, modulus)?.sub(&expand_expr_fp(b, vars, modulus)?))
        }
        PolyExpr::Mul(a, b) => {
            Ok(expand_expr_fp(a, vars, modulus)?.mul(&expand_expr_fp(b, vars, modulus)?))
        }
        PolyExpr::Pow(e, exp) => Ok(expand_expr_fp(e, vars, modulus)?.pow(*exp)),
    }
}
