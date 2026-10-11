//! Fp の法の素数性。Baillie–PSW(強い底2の Miller–Rabin と強い Lucas 検定)で判定する。
//! 2^64 未満では反例がないことが確かめられている。

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

pub fn is_prime(n: &BigUint) -> bool {
    let two = BigUint::from(2u32);
    if *n < two {
        return false;
    }
    for p in [2u32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
        let p = BigUint::from(p);
        if *n == p {
            return true;
        }
        if (n % &p).is_zero() {
            return false;
        }
    }
    strong_fermat_base2(n) && strong_lucas(n)
}

fn strong_fermat_base2(n: &BigUint) -> bool {
    let one = BigUint::one();
    let n1 = n - &one;
    let s = n1.trailing_zeros().unwrap_or(0);
    let d = &n1 >> s;
    let mut x = BigUint::from(2u32).modpow(&d, n);
    if x == one || x == n1 {
        return true;
    }
    for _ in 1..s {
        x = (&x * &x) % n;
        if x == n1 {
            return true;
        }
    }
    false
}

fn jacobi(a: &BigInt, n: &BigInt) -> i32 {
    let mut a = a.mod_floor(n);
    let mut n = n.clone();
    let mut result = 1;
    let three = BigInt::from(3);
    let five = BigInt::from(5);
    let eight = BigInt::from(8);
    let four = BigInt::from(4);
    while !a.is_zero() {
        while a.is_even() {
            a >>= 1;
            let r = n.mod_floor(&eight);
            if r == three || r == five {
                result = -result;
            }
        }
        std::mem::swap(&mut a, &mut n);
        if a.mod_floor(&four) == three && n.mod_floor(&four) == three {
            result = -result;
        }
        a = a.mod_floor(&n);
    }
    if n.is_one() { result } else { 0 }
}

fn strong_lucas(n: &BigUint) -> bool {
    let root = n.sqrt();
    if &root * &root == *n {
        return false;
    }
    let nn = BigInt::from_biguint(Sign::Plus, n.clone());
    let mut d = BigInt::from(5);
    loop {
        match jacobi(&d, &nn) {
            -1 => break,
            0 if d.abs() != nn => return false,
            _ => {}
        }
        d = if d.is_positive() {
            -(d + BigInt::from(2))
        } else {
            -(d - BigInt::from(2))
        };
    }
    let p = BigInt::one();
    let q: BigInt = (BigInt::one() - &d) / BigInt::from(4);
    let modn = |x: BigInt| x.mod_floor(&nn);
    let half = |x: BigInt| {
        let x = x.mod_floor(&nn);
        if x.is_odd() { (x + &nn) / 2 } else { x / 2 }
    };
    let n1 = n + BigUint::one();
    let s = n1.trailing_zeros().unwrap_or(0);
    let k = &n1 >> s;
    let bits = k.bits();
    let mut u = BigInt::one();
    let mut v = p.clone();
    let mut qk = modn(q.clone());
    for i in (0..bits.saturating_sub(1)).rev() {
        u = modn(&u * &v);
        v = modn(&v * &v - 2 * &qk);
        qk = modn(&qk * &qk);
        if k.bit(i) {
            let nu = half(&p * &u + &v);
            let nv = half(&d * &u + &p * &v);
            u = nu;
            v = nv;
            qk = modn(&qk * &q);
        }
    }
    if u.is_zero() || v.is_zero() {
        return true;
    }
    for _ in 1..s.to_u64().unwrap_or(0) {
        v = modn(&v * &v - 2 * &qk);
        qk = modn(&qk * &qk);
        if v.is_zero() {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn trial(n: u64) -> bool {
        n >= 2
            && (2..)
                .take_while(|d| d * d <= n)
                .all(|d| !n.is_multiple_of(d))
    }

    #[test]
    fn agrees_with_trial_division() {
        for n in 0u64..20000 {
            assert_eq!(is_prime(&BigUint::from(n)), trial(n), "n={n}");
        }
    }

    #[test]
    fn large_known_values() {
        let m127 = (BigUint::one() << 127u32) - BigUint::one();
        assert!(is_prime(&m127));
        assert!(!is_prime(&(&m127 * BigUint::from(3u32))));
        // 強い底2の擬素数(2047 = 23·89、3215031751)は Lucas 側で落ちる。
        assert!(!is_prime(&BigUint::from(2047u32)));
        assert!(!is_prime(&BigUint::from(3_215_031_751u64)));
    }
}
