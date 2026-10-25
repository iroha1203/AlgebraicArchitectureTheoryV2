//! 局所行列の正規化された有理係数。消去自体は既存field_fiberへ渡す。
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::ops::{Add, AddAssign, Mul, Sub, SubAssign};
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed::local_result) struct Q(BigInt, BigInt);
impl Q {
    fn new(n: BigInt, d: BigInt) -> Self {
        assert!(!d.is_zero());
        let g = n.gcd(&d);
        let (mut n, mut d) = (n / g.clone(), d / g);
        if d.is_negative() {
            n = -n;
            d = -d;
        }
        Self(n, d)
    }
    pub(in crate::observed::local_result) fn scalar(&self) -> crate::observed::result::Scalar {
        crate::observed::result::Scalar::Q(self.0.clone(), self.1.clone())
    }
    pub(super) fn from_scalar(
        v: &crate::observed::result::Scalar,
    ) -> Result<Self, crate::observed::result::ValidationFailure> {
        match v {
            crate::observed::result::Scalar::Q(n, d) if !d.is_zero() => {
                Ok(Self::new(n.clone(), d.clone()))
            }
            _ => Err("局所係数が有理数でない".into()),
        }
    }
}
impl From<BigInt> for Q {
    fn from(v: BigInt) -> Self {
        Self(v, BigInt::one())
    }
}
impl From<usize> for Q {
    fn from(v: usize) -> Self {
        Self::from(BigInt::from(v))
    }
}
impl Zero for Q {
    fn zero() -> Self {
        Self::from(BigInt::zero())
    }
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}
impl One for Q {
    fn one() -> Self {
        Self::from(BigInt::one())
    }
}
impl Add for Q {
    type Output = Q;
    fn add(self, r: Q) -> Q {
        &self + &r
    }
}
impl Sub for Q {
    type Output = Q;
    fn sub(self, r: Q) -> Q {
        &self - &r
    }
}
impl Mul for Q {
    type Output = Q;
    fn mul(self, r: Q) -> Q {
        &self * &r
    }
}
impl Add<&Q> for &Q {
    type Output = Q;
    fn add(self, r: &Q) -> Q {
        Q::new(&self.0 * &r.1 + &r.0 * &self.1, &self.1 * &r.1)
    }
}
impl Sub<&Q> for &Q {
    type Output = Q;
    fn sub(self, r: &Q) -> Q {
        Q::new(&self.0 * &r.1 - &r.0 * &self.1, &self.1 * &r.1)
    }
}
impl Mul<&Q> for &Q {
    type Output = Q;
    fn mul(self, r: &Q) -> Q {
        Q::new(&self.0 * &r.0, &self.1 * &r.1)
    }
}
impl AddAssign<&Q> for Q {
    fn add_assign(&mut self, r: &Q) {
        *self = &*self + r;
    }
}
impl SubAssign<&Q> for Q {
    fn sub_assign(&mut self, r: &Q) {
        *self = &*self - r;
    }
}
impl PartialOrd for Q {
    fn partial_cmp(&self, r: &Self) -> Option<std::cmp::Ordering> {
        Some((&self.0 * &r.1).cmp(&(&r.0 * &self.1)))
    }
}
impl std::fmt::Display for Q {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.0, self.1)
    }
}

impl Sub<Q> for &Q {
    type Output = Q;
    fn sub(self, r: Q) -> Q {
        self - &r
    }
}

impl std::ops::Neg for &Q {
    type Output = Q;
    fn neg(self) -> Q {
        Q(-&self.0, self.1.clone())
    }
}
