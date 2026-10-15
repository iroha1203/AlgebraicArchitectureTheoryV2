//! Fp の法の素数性。Baillie–PSW(強い底2の Miller–Rabin と強い Lucas 検定)で判定する。
//! 2^64 未満では反例がないことが確かめられている。

use crate::issue::Issue;
use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};
use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

pub fn is_prime(n: &BigUint) -> bool {
    is_prime_controlled::<Box<Issue>>(
        n,
        &mut Control::unlimited(),
        Checkpoint::DefinitionSemantics,
    )
    .expect("通常の素数性検査は中断しない")
}

/// 型検査と同じ制御で、crate 所有の反復と原始演算の前後を確認する。
pub(crate) fn is_prime_controlled<E: InputError>(
    n: &BigUint,
    control: &mut Control,
    point: Checkpoint,
) -> Result<bool, E> {
    E::checkpoint(control, point)?;
    let two = BigUint::from(2u32);
    if *n < two {
        return finish_decision::<E>(false, control, point);
    }
    for p in [2u32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
        E::checkpoint(control, point)?;
        let p = BigUint::from(p);
        if *n == p {
            return finish_decision::<E>(true, control, point);
        }
        if (n % &p).is_zero() {
            return finish_decision::<E>(false, control, point);
        }
        E::checkpoint(control, point)?;
    }
    if !strong_fermat_base2::<E>(n, control, point)? {
        return finish_decision::<E>(false, control, point);
    }
    let prime = strong_lucas::<E>(n, control, point)?;
    finish_decision::<E>(prime, control, point)
}

/// false は素数性全体の棄却が完了した場合だけ渡す。
/// 予算を観測しても既知の不正を呼出し元で構成できる。取消は常に優先する。
fn finish_decision<E: InputError>(
    prime: bool,
    control: &mut Control,
    point: Checkpoint,
) -> Result<bool, E> {
    match E::checkpoint(control, point) {
        Err(stop) if !prime && stop.is_budget_stop() => Ok(false),
        Err(stop) => Err(stop),
        Ok(()) => Ok(prime),
    }
}

fn strong_fermat_base2<E: InputError>(
    n: &BigUint,
    control: &mut Control,
    point: Checkpoint,
) -> Result<bool, E> {
    E::checkpoint(control, point)?;
    let one = BigUint::one();
    let n1 = n - &one;
    let s = n1.trailing_zeros().unwrap_or(0);
    let d = &n1 >> s;
    let mut x = BigUint::from(2u32).modpow(&d, n);
    if x == one || x == n1 {
        // Passing this test leaves the Lucas test unexamined.
        E::checkpoint(control, point)?;
        return Ok(true);
    }
    if s <= 1 {
        return finish_decision::<E>(false, control, point);
    }
    E::checkpoint(control, point)?;
    for i in 1..s {
        E::checkpoint(control, point)?;
        x = (&x * &x) % n;
        if x == n1 {
            E::checkpoint(control, point)?;
            return Ok(true);
        }
        if i + 1 == s {
            return finish_decision::<E>(false, control, point);
        }
        E::checkpoint(control, point)?;
    }
    unreachable!("少なくとも一度の反復が最終判定を返す")
}

fn jacobi<E: InputError>(
    a: &BigInt,
    n: &BigInt,
    control: &mut Control,
    point: Checkpoint,
) -> Result<i32, E> {
    E::checkpoint(control, point)?;
    // Only this zero is the very rejection used by the caller's Selfridge search.
    let zero_proves_composite = a.abs() != *n;
    let mut a = a.mod_floor(n);
    let mut n = n.clone();
    let mut result = 1;
    let three = BigInt::from(3);
    let five = BigInt::from(5);
    let eight = BigInt::from(8);
    let four = BigInt::from(4);
    if a.is_zero() {
        return finish_jacobi::<E>(
            if n.is_one() { result } else { 0 },
            zero_proves_composite,
            control,
            point,
        );
    }
    E::checkpoint(control, point)?;
    while !a.is_zero() {
        E::checkpoint(control, point)?;
        while a.is_even() {
            E::checkpoint(control, point)?;
            a >>= 1;
            let r = n.mod_floor(&eight);
            if r == three || r == five {
                result = -result;
            }
            E::checkpoint(control, point)?;
        }
        std::mem::swap(&mut a, &mut n);
        if a.mod_floor(&four) == three && n.mod_floor(&four) == three {
            result = -result;
        }
        a = a.mod_floor(&n);
        if a.is_zero() {
            return finish_jacobi::<E>(
                if n.is_one() { result } else { 0 },
                zero_proves_composite,
                control,
                point,
            );
        }
        E::checkpoint(control, point)?;
    }
    finish_jacobi::<E>(
        if n.is_one() { result } else { 0 },
        zero_proves_composite,
        control,
        point,
    )
}

fn finish_jacobi<E: InputError>(
    symbol: i32,
    zero_proves_composite: bool,
    control: &mut Control,
    point: Checkpoint,
) -> Result<i32, E> {
    match E::checkpoint(control, point) {
        Err(stop) if symbol == 0 && zero_proves_composite && stop.is_budget_stop() => Ok(0),
        Err(stop) => Err(stop),
        Ok(()) => Ok(symbol),
    }
}

fn strong_lucas<E: InputError>(
    n: &BigUint,
    control: &mut Control,
    point: Checkpoint,
) -> Result<bool, E> {
    E::checkpoint(control, point)?;
    let root = n.sqrt();
    if &root * &root == *n {
        return finish_decision::<E>(false, control, point);
    }
    E::checkpoint(control, point)?;
    let nn = BigInt::from_biguint(Sign::Plus, n.clone());
    let mut d = BigInt::from(5);
    loop {
        E::checkpoint(control, point)?;
        match jacobi::<E>(&d, &nn, control, point)? {
            -1 => {
                E::checkpoint(control, point)?;
                break;
            }
            0 if d.abs() != nn => return finish_decision::<E>(false, control, point),
            _ => {}
        }
        d = if d.is_positive() {
            -(d + BigInt::from(2))
        } else {
            -(d - BigInt::from(2))
        };
        E::checkpoint(control, point)?;
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
    E::checkpoint(control, point)?;
    for i in (0..bits.saturating_sub(1)).rev() {
        E::checkpoint(control, point)?;
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
        if i == 0 && s <= 1 {
            // With no remaining squarings, this bit completes the whole test.
            return finish_decision::<E>(u.is_zero() || v.is_zero(), control, point);
        }
        E::checkpoint(control, point)?;
    }
    if u.is_zero() || v.is_zero() {
        return finish_decision::<E>(true, control, point);
    }
    for i in 1..s.to_u64().unwrap_or(0) {
        E::checkpoint(control, point)?;
        v = modn(&v * &v - 2 * &qk);
        qk = modn(&qk * &qk);
        if v.is_zero() {
            return finish_decision::<E>(true, control, point);
        }
        if i + 1 == s {
            return finish_decision::<E>(false, control, point);
        }
        E::checkpoint(control, point)?;
    }
    finish_decision::<E>(false, control, point)
}

#[cfg(test)]
mod tests {
    use super::*;

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

#[cfg(test)]
mod controlled_tests {
    use super::*;
    use crate::observed::control::{CheckFailure, Limits, Resource, StopReason, Usage};
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};

    type Failure = CheckFailure<Box<Issue>>;
    const POINT: Checkpoint = Checkpoint::LawSemantics;

    fn probe(at: usize, mode: usize) -> (Control, Rc<Cell<usize>>) {
        let visits = Rc::new(Cell::new(0));
        let seen = visits.clone();
        let control = Control::new(
            Limits {
                time_ms: (mode == 1).then_some(3),
                memory_mib: (mode == 2).then_some(5),
            },
            move |point| {
                assert_eq!(point, POINT);
                seen.set(seen.get() + 1);
                let stop = seen.get() == at;
                Usage {
                    elapsed_ms: if stop && mode == 1 { 7 } else { 0 },
                    memory_mib: if stop && mode == 2 { 11 } else { 0 },
                    signal: (stop && mode == 0).then_some(Signal::Int),
                }
            },
        );
        (control, visits)
    }

    fn expected_reason(mode: usize) -> StopReason {
        match mode {
            0 => StopReason::Cancelled(Signal::Int),
            1 => StopReason::BudgetExhausted {
                resource: Resource::TimeMs,
                limit: 3,
                observed: 7,
            },
            2 => StopReason::BudgetExhausted {
                resource: Resource::MemoryMib,
                limit: 5,
                observed: 11,
            },
            _ => unreachable!(),
        }
    }

    fn accepted_stage(stage: usize, control: &mut Control) -> Result<bool, Failure> {
        match stage {
            0 => is_prime_controlled::<Failure>(&101u32.into(), control, POINT),
            1 => strong_fermat_base2::<Failure>(&101u32.into(), control, POINT),
            2 => jacobi::<Failure>(&5.into(), &101.into(), control, POINT).map(|_| true),
            3 => strong_lucas::<Failure>(&101u32.into(), control, POINT),
            4 => strong_lucas::<Failure>(&127u32.into(), control, POINT),
            _ => unreachable!(),
        }
    }

    #[test]
    fn small_values_preserve_the_existing_primality_decisions() {
        for n in [
            0u32, 1, 2, 3, 4, 47, 49, 53, 65, 91, 97, 101, 121, 143, 169, 221, 257,
        ] {
            // An independent small trial-division oracle; no large-number fixture.
            let expected = n >= 2 && !(2..n).any(|factor| n % factor == 0);
            assert_eq!(is_prime(&n.into()), expected, "{n}");
            assert_eq!(
                is_prime_controlled::<Failure>(&n.into(), &mut Control::unlimited(), POINT,)
                    .unwrap(),
                expected,
                "{n}",
            );
        }
    }

    #[test]
    fn prime_internal_iteration_stops_keep_the_shared_reason() {
        // 101 traverses the small-prime loop, Fermat squaring, Jacobi's
        // nested loops, Selfridge search and Lucas bits. 127 additionally
        // traverses Lucas's final squaring loop (127 + 1 has seven factors 2).
        for stage in 0..5 {
            let (mut baseline, total) = probe(usize::MAX, 0);
            assert!(accepted_stage(stage, &mut baseline).unwrap());
            assert!(total.get() > 2, "stage {stage}");
            for at in 1..=total.get() {
                for mode in 0..3 {
                    let (mut control, seen) = probe(at, mode);
                    let error = accepted_stage(stage, &mut control).unwrap_err();
                    assert_eq!(seen.get(), at, "stage {stage} at {at}");
                    assert!(
                        matches!(error, Failure::Stopped(ref reason) if *reason == expected_reason(mode))
                    );
                    assert_eq!(control.stop_reason(), Some(expected_reason(mode)));
                }
            }
        }
    }

    fn rejected_stage(stage: usize, control: &mut Control) -> Result<bool, Failure> {
        match stage {
            0 => is_prime_controlled::<Failure>(&49u32.into(), control, POINT),
            1 => strong_fermat_base2::<Failure>(&65u32.into(), control, POINT),
            2 => strong_lucas::<Failure>(&9u32.into(), control, POINT),
            3 => strong_lucas::<Failure>(&35u32.into(), control, POINT),
            4 => strong_lucas::<Failure>(&77u32.into(), control, POINT),
            5 => strong_lucas::<Failure>(&143u32.into(), control, POINT),
            6 => jacobi::<Failure>(&5.into(), &15.into(), control, POINT).map(|symbol| symbol != 0),
            _ => unreachable!(),
        }
    }

    #[test]
    fn completed_composite_rejections_survive_only_budget_at_terminal_checks() {
        // Distinct terminal rejections: divisor, Fermat exhaustion, square,
        // Jacobi zero, final Lucas bit, and final Lucas squaring.
        for stage in 0..7 {
            let (mut baseline, total) = probe(usize::MAX, 0);
            assert!(
                !rejected_stage(stage, &mut baseline).unwrap(),
                "stage {stage}"
            );
            for mode in 0..3 {
                let (mut control, seen) = probe(total.get(), mode);
                let result = rejected_stage(stage, &mut control);
                assert_eq!(seen.get(), total.get());
                if mode == 0 {
                    assert!(matches!(
                        result,
                        Err(Failure::Stopped(StopReason::Cancelled(Signal::Int)))
                    ));
                } else {
                    assert!(!result.unwrap(), "stage {stage}");
                }
                assert_eq!(control.stop_reason(), Some(expected_reason(mode)));
            }
            // An unexamined stage never inherits a later composite answer.
            let (mut control, _) = probe(1, 1);
            assert!(matches!(
                rejected_stage(stage, &mut control),
                Err(Failure::Stopped(_))
            ));
        }
    }

    #[test]
    fn jacobi_zero_equal_to_the_modulus_does_not_become_a_composite_answer() {
        let (mut baseline, total) = probe(usize::MAX, 0);
        assert_eq!(
            jacobi::<Failure>(&5.into(), &5.into(), &mut baseline, POINT).unwrap(),
            0
        );
        for mode in 0..3 {
            let (mut control, _) = probe(total.get(), mode);
            let result = jacobi::<Failure>(&5.into(), &5.into(), &mut control, POINT);
            assert!(
                matches!(result, Err(Failure::Stopped(ref reason)) if *reason == expected_reason(mode))
            );
        }
        // A genuinely composite Selfridge result may pass its zero through
        // the enclosing loop without losing the already sampled budget.
        let (mut baseline, total) = probe(usize::MAX, 0);
        assert!(!strong_lucas::<Failure>(&35u32.into(), &mut baseline, POINT).unwrap());
        for at in total.get() - 1..=total.get() {
            let (mut control, _) = probe(at, 1);
            assert!(!strong_lucas::<Failure>(&35u32.into(), &mut control, POINT).unwrap());
            assert_eq!(control.stop_reason(), Some(expected_reason(1)));
        }
    }
}
