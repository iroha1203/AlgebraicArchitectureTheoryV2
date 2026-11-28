//! 正確なスカラー演算（任意精度有理数 `Rat`、素数体 `FpElem`、共通環トレイト `RingCoeff`）。

use crate::ir::term::ScalarLit;
use archsig_common::prime::is_prime;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// 多項式係数として扱う可換環要素の共通演算。
pub trait RingCoeff: Clone + Eq + fmt::Debug + fmt::Display {
    fn coeff_is_zero(&self) -> bool;
    fn coeff_is_one(&self) -> bool;
    fn add_ref(&self, other: &Self) -> Self;
    fn sub_ref(&self, other: &Self) -> Self;
    fn mul_ref(&self, other: &Self) -> Self;
    fn neg_ref(&self) -> Self;
    /// 同じ環（同じ法 `p` 等）に属する零元を返す。
    fn zero_like(&self) -> Self;
    /// 同じ環に属する単位元 `1` を返す。
    fn one_like(&self) -> Self;
    /// 同じ環に属する非負整数 `n * 1` を返す（標数 `p` では自動的に `n mod p`）。
    fn u32_like(&self, n: u32) -> Self {
        let mut acc = self.zero_like();
        let mut base = self.one_like();
        let mut k = n;
        while k > 0 {
            if k & 1 == 1 {
                acc = acc.add_ref(&base);
            }
            k >>= 1;
            if k > 0 {
                base = base.add_ref(&base);
            }
        }
        acc
    }
    /// 2 つの係数が同じ係数環（特に `FpElem` の同一素数法）に属するか判定する。
    fn same_ring(&self, _other: &Self) -> bool {
        true
    }
    /// 係数の多倍長整数表現における最大ビット長を返す。
    fn coeff_max_bits(&self) -> u64;
}

impl RingCoeff for BigInt {
    fn coeff_is_zero(&self) -> bool {
        Zero::is_zero(self)
    }

    fn coeff_is_one(&self) -> bool {
        One::is_one(self)
    }

    fn add_ref(&self, other: &Self) -> Self {
        self + other
    }

    fn sub_ref(&self, other: &Self) -> Self {
        self - other
    }

    fn mul_ref(&self, other: &Self) -> Self {
        self * other
    }

    fn neg_ref(&self) -> Self {
        -self
    }

    fn zero_like(&self) -> Self {
        BigInt::zero()
    }

    fn one_like(&self) -> Self {
        BigInt::one()
    }

    fn coeff_max_bits(&self) -> u64 {
        self.bits()
    }
}

/// 任意精度の既約有理数（不変条件: `den > 0`、`gcd(|num|, den) == 1`、`0` は `0/1`）。
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rat {
    num: BigInt,
    den: BigInt,
}

impl Ord for Rat {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // 不変条件 `den > 0` より `a/b <=> c/d` は `a*d <=> c*b` と同値。
        (&self.num * &other.den).cmp(&(&other.num * &self.den))
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Rat {
    pub fn zero() -> Self {
        Self {
            num: BigInt::zero(),
            den: BigInt::one(),
        }
    }

    pub fn one() -> Self {
        Self {
            num: BigInt::one(),
            den: BigInt::one(),
        }
    }

    pub fn from_int(n: impl Into<BigInt>) -> Self {
        Self {
            num: n.into(),
            den: BigInt::one(),
        }
    }

    pub fn new(num: impl Into<BigInt>, den: impl Into<BigInt>) -> Option<Self> {
        let mut n = num.into();
        let mut d = den.into();
        if d.is_zero() {
            return None;
        }
        if d.is_negative() {
            n = -n;
            d = -d;
        }
        if n.is_zero() {
            return Some(Self::zero());
        }
        let g = n.gcd(&d);
        Some(Self {
            num: n / &g,
            den: d / g,
        })
    }

    pub fn num(&self) -> &BigInt {
        &self.num
    }

    pub fn den(&self) -> &BigInt {
        &self.den
    }

    pub fn is_zero(&self) -> bool {
        self.num.is_zero()
    }

    pub fn is_one(&self) -> bool {
        self.num.is_one() && self.den.is_one()
    }

    pub fn is_neg_one(&self) -> bool {
        self.num == BigInt::from(-1) && self.den.is_one()
    }

    pub fn is_negative(&self) -> bool {
        self.num.is_negative()
    }

    pub fn inv(&self) -> Option<Self> {
        if self.num.is_zero() {
            None
        } else {
            Self::new(self.den.clone(), self.num.clone())
        }
    }

    pub fn to_scalar_lit(&self) -> ScalarLit {
        ScalarLit::Q {
            num: self.num.clone(),
            den: self.den.clone(),
        }
    }
}

impl Neg for Rat {
    type Output = Rat;
    fn neg(self) -> Rat {
        Rat {
            num: -self.num,
            den: self.den,
        }
    }
}

impl Neg for &Rat {
    type Output = Rat;
    fn neg(self) -> Rat {
        Rat {
            num: -&self.num,
            den: self.den.clone(),
        }
    }
}

impl Add for &Rat {
    type Output = Rat;
    fn add(self, rhs: &Rat) -> Rat {
        if self.is_zero() {
            return rhs.clone();
        }
        if rhs.is_zero() {
            return self.clone();
        }
        let g = self.den.gcd(&rhs.den);
        let lhs_scale = &rhs.den / &g;
        let rhs_scale = &self.den / &g;
        let num = &self.num * &lhs_scale + &rhs.num * &rhs_scale;
        let den = &self.den * &lhs_scale;
        Rat::new(num, den).expect("product of positive denominators is positive")
    }
}

impl Add for Rat {
    type Output = Rat;
    fn add(self, rhs: Rat) -> Rat {
        &self + &rhs
    }
}

impl Sub for &Rat {
    type Output = Rat;
    fn sub(self, rhs: &Rat) -> Rat {
        self + &(-rhs)
    }
}

impl Sub for Rat {
    type Output = Rat;
    fn sub(self, rhs: Rat) -> Rat {
        &self - &rhs
    }
}

impl Mul for &Rat {
    type Output = Rat;
    fn mul(self, rhs: &Rat) -> Rat {
        if self.is_zero() || rhs.is_zero() {
            return Rat::zero();
        }
        let g1 = self.num.gcd(&rhs.den);
        let g2 = rhs.num.gcd(&self.den);
        Rat {
            num: (&self.num / &g1) * (&rhs.num / &g2),
            den: (&self.den / &g2) * (&rhs.den / &g1),
        }
    }
}

impl Mul for Rat {
    type Output = Rat;
    fn mul(self, rhs: Rat) -> Rat {
        &self * &rhs
    }
}

impl Div for &Rat {
    type Output = Option<Rat>;
    fn div(self, rhs: &Rat) -> Option<Rat> {
        rhs.inv().map(|inv| self * &inv)
    }
}

impl RingCoeff for Rat {
    fn coeff_is_zero(&self) -> bool {
        Rat::is_zero(self)
    }

    fn coeff_is_one(&self) -> bool {
        Rat::is_one(self)
    }

    fn add_ref(&self, other: &Self) -> Self {
        self + other
    }

    fn sub_ref(&self, other: &Self) -> Self {
        self - other
    }

    fn mul_ref(&self, other: &Self) -> Self {
        self * other
    }

    fn neg_ref(&self) -> Self {
        -self
    }

    fn zero_like(&self) -> Self {
        Rat::zero()
    }

    fn one_like(&self) -> Self {
        Rat::one()
    }

    fn coeff_max_bits(&self) -> u64 {
        self.num.bits().max(self.den.bits())
    }
}

impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den.is_one() {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

/// 素数体 `F_p` の元（不変条件: `p` は素数、`0 <= value < p`）。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FpElem {
    value: BigUint,
    modulus: BigUint,
}

impl FpElem {
    /// 素数 `modulus` を検証して `F_p` の元を作る。非素数なら `None`。
    pub fn new(value: BigInt, modulus: BigUint) -> Option<Self> {
        if !is_prime(&modulus) {
            return None;
        }
        Some(Self::from_checked_prime(value, modulus))
    }

    /// 素数性検証済みの法から元を作る（内部用）。
    pub(crate) fn from_checked_prime(value: BigInt, modulus: BigUint) -> Self {
        debug_assert!(is_prime(&modulus));
        let m_signed = BigInt::from(modulus.clone());
        let reduced = value.mod_floor(&m_signed);
        let (_, mag) = reduced.into_parts();
        Self {
            value: mag,
            modulus,
        }
    }

    pub fn zero(modulus: BigUint) -> Option<Self> {
        Self::new(BigInt::zero(), modulus)
    }

    pub fn one(modulus: BigUint) -> Option<Self> {
        Self::new(BigInt::one(), modulus)
    }

    pub fn value(&self) -> &BigUint {
        &self.value
    }

    pub fn modulus(&self) -> &BigUint {
        &self.modulus
    }

    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    pub fn is_one(&self) -> bool {
        self.value.is_one()
    }

    pub fn add_checked(&self, other: &Self) -> Option<Self> {
        if self.modulus != other.modulus {
            return None;
        }
        let sum = (&self.value + &other.value) % &self.modulus;
        Some(Self {
            value: sum,
            modulus: self.modulus.clone(),
        })
    }

    pub fn sub_checked(&self, other: &Self) -> Option<Self> {
        if self.modulus != other.modulus {
            return None;
        }
        let diff = if self.value >= other.value {
            &self.value - &other.value
        } else {
            &self.modulus - (&other.value - &self.value)
        };
        Some(Self {
            value: diff,
            modulus: self.modulus.clone(),
        })
    }

    pub fn mul_checked(&self, other: &Self) -> Option<Self> {
        if self.modulus != other.modulus {
            return None;
        }
        let prod = (&self.value * &other.value) % &self.modulus;
        Some(Self {
            value: prod,
            modulus: self.modulus.clone(),
        })
    }

    pub fn neg_elem(&self) -> Self {
        if self.value.is_zero() {
            self.clone()
        } else {
            Self {
                value: &self.modulus - &self.value,
                modulus: self.modulus.clone(),
            }
        }
    }

    /// 拡張ユークリッド互除法による逆元。零元なら `None`。
    pub fn inv(&self) -> Option<Self> {
        if self.value.is_zero() {
            return None;
        }
        let a = BigInt::from(self.value.clone());
        let p = BigInt::from(self.modulus.clone());
        let egcd = a.extended_gcd(&p);
        if !egcd.gcd.is_one() {
            return None;
        }
        Some(Self::from_checked_prime(egcd.x, self.modulus.clone()))
    }
}

impl RingCoeff for FpElem {
    fn coeff_is_zero(&self) -> bool {
        FpElem::is_zero(self)
    }

    fn coeff_is_one(&self) -> bool {
        FpElem::is_one(self)
    }

    fn add_ref(&self, other: &Self) -> Self {
        self.add_checked(other)
            .expect("FpElem operands in a polynomial ring share the same prime modulus")
    }

    fn sub_ref(&self, other: &Self) -> Self {
        self.sub_checked(other)
            .expect("FpElem operands in a polynomial ring share the same prime modulus")
    }

    fn mul_ref(&self, other: &Self) -> Self {
        self.mul_checked(other)
            .expect("FpElem operands in a polynomial ring share the same prime modulus")
    }

    fn neg_ref(&self) -> Self {
        self.neg_elem()
    }

    fn zero_like(&self) -> Self {
        Self {
            value: BigUint::zero(),
            modulus: self.modulus.clone(),
        }
    }

    fn one_like(&self) -> Self {
        Self {
            value: BigUint::one(),
            modulus: self.modulus.clone(),
        }
    }

    fn same_ring(&self, other: &Self) -> bool {
        self.modulus == other.modulus
    }

    fn coeff_max_bits(&self) -> u64 {
        self.value.bits().max(self.modulus.bits())
    }
}

impl fmt::Display for FpElem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
