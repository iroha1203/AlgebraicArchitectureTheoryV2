//! 観測値と再検査が共有する正確な数値演算。型間の暗黙変換は行わない。

use super::{
    control::{Checkpoint, Control},
    result::{Scalar, ValidationFailure},
};
use crate::{
    archmap::Value,
    law::ast::{BinOp, UnOp},
    types::Type,
};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

fn tick(control: &Control) -> Result<(), ValidationFailure> {
    control
        .clone()
        .checkpoint(Checkpoint::FiniteIteration)
        .map_err(ValidationFailure::Stop)
}

/// 再帰・原始演算の前後に同じ制御を照合する。停止理由は置換しない。
fn controlled<T>(
    control: &Control,
    work: impl FnOnce() -> Result<T, ValidationFailure>,
) -> Result<T, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(control)?;
        let value = work()?;
        tick(control)?;
        Ok(value)
    })
}

pub(crate) fn is_numeric_type(ty: &Type, control: &Control) -> Result<bool, ValidationFailure> {
    controlled(control, || match ty {
        Type::Z | Type::Q | Type::Fp(_) => Ok(true),
        Type::Tuple(items) => {
            for item in items {
                tick(control)?;
                let numeric = is_numeric_type(item, control)?;
                tick(control)?;
                if !numeric {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    })
}

/// literal と宣言した法は符号のない正規10進表記を用いる。
fn natural(text: &str, control: &Control) -> Result<BigInt, ValidationFailure> {
    controlled(control, || {
        if text.is_empty() || (text.len() > 1 && text.starts_with('0')) {
            return Err("数値の10進表記が正規形でない".into());
        }
        for byte in text.bytes() {
            tick(control)?;
            let digit = byte.is_ascii_digit();
            tick(control)?;
            if !digit {
                return Err("数値の10進表記に数字以外を含む".into());
            }
        }
        text.parse()
            .map_err(|_| ValidationFailure::Internal("数値の10進表記を読めない".into()))
    })
}

fn modulus(text: &str, control: &Control) -> Result<BigInt, ValidationFailure> {
    controlled(control, || {
        let p = natural(text, control)?;
        if !p.is_positive() {
            return Err("Fp の法が正でない".into());
        }
        Ok(p)
    })
}

fn gcd(n: &BigInt, d: &BigInt, control: &Control) -> Result<BigInt, ValidationFailure> {
    controlled(control, || {
        let (mut a, mut b) = (n.abs(), d.abs());
        loop {
            tick(control)?;
            if b.is_zero() {
                tick(control)?;
                return Ok(a);
            }
            let remainder = &a % &b;
            a = b;
            b = remainder;
            tick(control)?;
        }
    })
}

fn reduced(n: BigInt, d: BigInt, control: &Control) -> Result<Scalar, ValidationFailure> {
    controlled(control, || {
        if !d.is_positive() {
            return Err("Q の分母が正でない".into());
        }
        let divisor = gcd(&n, &d, control)?;
        Ok(Scalar::Q(n / &divisor, d / divisor))
    })
}

fn numeric_check(value: &Scalar, control: &Control) -> Result<(), ValidationFailure> {
    controlled(control, || match value {
        Scalar::Z(_) => Ok(()),
        Scalar::Q(n, d) => {
            if !d.is_positive() || !gcd(n, d, control)?.is_one() {
                return Err("Q の値が正分母の既約形でない".into());
            }
            Ok(())
        }
        Scalar::Fp { modulus: p, value } => {
            let p = modulus(p, control)?;
            if value.is_negative() || value >= &p {
                return Err("Fp の値が法の正規剰余でない".into());
            }
            Ok(())
        }
        Scalar::Tuple(items) => {
            for item in items {
                tick(control)?;
                numeric_check(item, control)?;
                tick(control)?;
            }
            Ok(())
        }
        _ => Err("数値Tupleに数値以外の成分がある".into()),
    })
}

pub(crate) fn check(value: &Scalar, control: &Control) -> Result<(), ValidationFailure> {
    controlled(control, || match value {
        Scalar::Bool(_) | Scalar::Subject { .. } => Ok(()),
        _ => numeric_check(value, control),
    })
}

pub(crate) fn literal(
    text: &str,
    ty: &Type,
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    controlled(control, || {
        let n = natural(text, control)?;
        match ty {
            Type::Z => Ok(Scalar::Z(n)),
            Type::Q => Ok(Scalar::Q(n, BigInt::one())),
            Type::Fp(p) => {
                if n >= modulus(p, control)? {
                    return Err("整数literalがFpの範囲外".into());
                }
                Ok(Scalar::Fp {
                    modulus: p.clone(),
                    value: n,
                })
            }
            _ => Err("整数literalの期待型がZ/Q/Fpでない".into()),
        }
    })
}

pub(crate) fn rational(
    n: &Scalar,
    d: &Scalar,
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    controlled(control, || match (n, d) {
        (Scalar::Z(n), Scalar::Z(d)) => reduced(n.clone(), d.clone(), control),
        _ => Err("ratの引数がZでない".into()),
    })
}

pub(crate) fn unary(
    op: UnOp,
    value: &Scalar,
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    controlled(control, || {
        if op != UnOp::Neg {
            return Err("数値の単項演算が負号でない".into());
        }
        numeric_check(value, control)?;
        negate(value, control)
    })
}

fn negate(value: &Scalar, control: &Control) -> Result<Scalar, ValidationFailure> {
    controlled(control, || match value {
        Scalar::Z(n) => Ok(Scalar::Z(-n)),
        Scalar::Q(n, d) => Ok(Scalar::Q(-n, d.clone())),
        Scalar::Fp { modulus: p, value } => {
            let p_value = modulus(p, control)?;
            Ok(Scalar::Fp {
                modulus: p.clone(),
                value: if value.is_zero() {
                    BigInt::zero()
                } else {
                    p_value - value
                },
            })
        }
        Scalar::Tuple(items) => {
            let mut result = Vec::with_capacity(items.len());
            for item in items {
                tick(control)?;
                result.push(negate(item, control)?);
                tick(control)?;
            }
            Ok(Scalar::Tuple(result))
        }
        _ => Err("数値以外の負号".into()),
    })
}

/// 等値と順序はBoolを返す。Tupleの等値は全成分を照合して型の相違も拒否する。
pub(crate) fn binary(
    op: BinOp,
    left: &Scalar,
    right: &Scalar,
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    controlled(control, || {
        numeric_check(left, control)?;
        numeric_check(right, control)?;
        binary_inner(op, left, right, control)
    })
}

fn binary_inner(
    op: BinOp,
    left: &Scalar,
    right: &Scalar,
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    controlled(control, || match (left, right) {
        (Scalar::Z(a), Scalar::Z(b)) => match op {
            BinOp::Add => Ok(Scalar::Z(a + b)),
            BinOp::Sub => Ok(Scalar::Z(a - b)),
            BinOp::Mul => Ok(Scalar::Z(a * b)),
            _ => comparison(op, a, b),
        },
        (Scalar::Q(an, ad), Scalar::Q(bn, bd)) => match op {
            BinOp::Add => reduced(an * bd + bn * ad, ad * bd, control),
            BinOp::Sub => reduced(an * bd - bn * ad, ad * bd, control),
            BinOp::Mul => reduced(an * bn, ad * bd, control),
            _ => comparison(op, &(an * bd), &(bn * ad)),
        },
        (
            Scalar::Fp {
                modulus: ap,
                value: a,
            },
            Scalar::Fp {
                modulus: bp,
                value: b,
            },
        ) => {
            if ap != bp {
                return Err("Fp演算の法が異なる".into());
            }
            let raw = match op {
                BinOp::Add => a + b,
                BinOp::Sub => a - b,
                BinOp::Mul => a * b,
                BinOp::Eq | BinOp::Ne => return comparison(op, a, b),
                _ => return Err("Fpに順序・論理演算を適用できない".into()),
            };
            let p = modulus(ap, control)?;
            let mut value = raw % &p;
            if value.is_negative() {
                value += &p;
            }
            Ok(Scalar::Fp {
                modulus: ap.clone(),
                value,
            })
        }
        (Scalar::Tuple(a), Scalar::Tuple(b)) => {
            if a.len() != b.len() {
                return Err("数値Tuple演算の成分数が異なる".into());
            }
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => {
                    let mut result = Vec::with_capacity(a.len());
                    for (left, right) in a.iter().zip(b) {
                        tick(control)?;
                        result.push(binary_inner(op, left, right, control)?);
                        tick(control)?;
                    }
                    Ok(Scalar::Tuple(result))
                }
                BinOp::Eq | BinOp::Ne => {
                    let mut equal = true;
                    for (left, right) in a.iter().zip(b) {
                        tick(control)?;
                        match binary_inner(BinOp::Eq, left, right, control)? {
                            Scalar::Bool(item_equal) => equal &= item_equal,
                            _ => return Err("数値等値の戻り値がBoolでない".into()),
                        }
                        tick(control)?;
                    }
                    Ok(Scalar::Bool(if op == BinOp::Eq { equal } else { !equal }))
                }
                _ => Err("数値Tupleに順序・論理演算を適用できない".into()),
            }
        }
        _ => Err("数値演算の型またはTupleの形が異なる".into()),
    })
}

fn comparison(op: BinOp, left: &BigInt, right: &BigInt) -> Result<Scalar, ValidationFailure> {
    Ok(Scalar::Bool(match op {
        BinOp::Eq => left == right,
        BinOp::Ne => left != right,
        BinOp::Lt => left < right,
        BinOp::Le => left <= right,
        BinOp::Gt => left > right,
        BinOp::Ge => left >= right,
        _ => return Err("数値の比較演算でない".into()),
    }))
}

pub(crate) fn from_input(
    value: &Value,
    ty: &Type,
    control: &Control,
) -> Result<Option<Scalar>, ValidationFailure> {
    controlled(control, || {
        if !is_numeric_type(ty, control)? {
            return Ok(None);
        }
        let scalar = input_numeric(value, ty, control)?;
        numeric_check(&scalar, control)?;
        Ok(Some(scalar))
    })
}

fn input_numeric(value: &Value, ty: &Type, control: &Control) -> Result<Scalar, ValidationFailure> {
    controlled(control, || match (value, ty) {
        (Value::Z(n), Type::Z) => Ok(Scalar::Z(n.clone())),
        (Value::Q(n, d), Type::Q) => Ok(Scalar::Q(n.clone(), d.clone())),
        (Value::Fp(n), Type::Fp(p)) => Ok(Scalar::Fp {
            modulus: p.clone(),
            value: BigInt::from(n.clone()),
        }),
        (Value::Tuple(values), Type::Tuple(types)) => {
            if values.len() != types.len() {
                return Err("原始数値Tupleの成分数と型が異なる".into());
            }
            let mut result = Vec::with_capacity(values.len());
            for (value, ty) in values.iter().zip(types) {
                tick(control)?;
                result.push(input_numeric(value, ty, control)?);
                tick(control)?;
            }
            Ok(Scalar::Tuple(result))
        }
        _ => Err("原始数値の値と宣言型が異なる".into()),
    })
}
