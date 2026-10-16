//! 欠測した元fieldのidentityを保つ、Z/Qだけの内部アフィン算術。

use super::{
    control::{Checkpoint, Control},
    numeric,
    result::{Fact, Scalar, ValidationFailure},
};
use crate::{
    law::ast::{BinOp, UnOp},
    types::Type,
};
use num_traits::{One, Zero};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Form {
    ty: Type,
    constant: Scalar,
    coefficients: BTreeMap<Fact, Scalar>,
}

fn tick(control: &Control) -> Result<(), ValidationFailure> {
    control
        .clone()
        .checkpoint(Checkpoint::FiniteIteration)
        .map_err(ValidationFailure::Stop)
}

fn controlled<T>(
    control: &Control,
    work: impl FnOnce() -> Result<T, ValidationFailure>,
) -> Result<T, ValidationFailure> {
    tick(control)?;
    let value = work()?;
    tick(control)?;
    Ok(value)
}

fn fact_check(fact: &Fact) -> Result<(), ValidationFailure> {
    if fact.snapshot.is_empty()
        || fact.subject.is_empty()
        || fact.field.as_ref().is_none_or(String::is_empty)
        || fact.atom.is_some()
    {
        return Err("アフィン欠測slotの元Factがfieldのidentityでない".into());
    }
    Ok(())
}

fn scalar_check(value: &Scalar, ty: &Type, control: &Control) -> Result<(), ValidationFailure> {
    controlled(control, || {
        if !matches!(
            (value, ty),
            (Scalar::Z(_), Type::Z) | (Scalar::Q(_, _), Type::Q)
        ) {
            return Err("アフィン係数または定数項の型がZ/Qの宣言型と異なる".into());
        }
        numeric::check(value, control)
    })
}

fn is_zero(value: &Scalar) -> Result<bool, ValidationFailure> {
    match value {
        Scalar::Z(n) | Scalar::Q(n, _) => Ok(n.is_zero()),
        _ => Err("アフィン係数または定数項がZ/Qでない".into()),
    }
}

impl Form {
    fn check(&self, control: &Control) -> Result<(), ValidationFailure> {
        controlled(control, || {
            scalar_check(&self.constant, &self.ty, control)?;
            for (fact, coefficient) in &self.coefficients {
                tick(control)?;
                fact_check(fact)?;
                scalar_check(coefficient, &self.ty, control)?;
                if is_zero(coefficient)? {
                    return Err("アフィン正規形に零係数が残っている".into());
                }
                tick(control)?;
            }
            Ok(())
        })
    }

    /// すべての元slot係数が消えた場合だけ通常値を返す。
    pub(crate) fn value(&self, control: &Control) -> Result<Option<Scalar>, ValidationFailure> {
        controlled(control, || {
            self.check(control)?;
            if !self.coefficients.is_empty() {
                return Ok(None);
            }
            tick(control)?;
            #[cfg(test)]
            observe(TestPoint::Constant);
            tick(control)?;
            let value = self.constant.clone();
            tick(control)?;
            Ok(Some(value))
        })
    }
}

pub(crate) fn constant(
    value: &Scalar,
    control: &Control,
) -> Result<Option<Form>, ValidationFailure> {
    controlled(control, || {
        let ty = match value {
            Scalar::Z(_) => Type::Z,
            Scalar::Q(_, _) => Type::Q,
            _ => return Ok(None),
        };
        scalar_check(value, &ty, control)?;
        Ok(Some(Form {
            ty,
            constant: value.clone(),
            coefficients: BTreeMap::new(),
        }))
    })
}

pub(crate) fn missing(
    ty: &Type,
    fact: &Fact,
    control: &Control,
) -> Result<Option<Form>, ValidationFailure> {
    controlled(control, || {
        if !matches!(ty, Type::Z | Type::Q) {
            return Ok(None);
        }
        fact_check(fact)?;
        let one = match ty {
            Type::Z => Scalar::Z(One::one()),
            Type::Q => Scalar::Q(One::one(), One::one()),
            _ => return Err("アフィン欠測slotの型がZ/Qでない".into()),
        };
        let mut coefficients = BTreeMap::new();
        tick(control)?;
        coefficients.insert(fact.clone(), one);
        tick(control)?;
        Ok(Some(Form {
            ty: ty.clone(),
            constant: numeric::zero(ty, control)?,
            coefficients,
        }))
    })
}

/// 同じ元slotの係数を加算し、正確な零はmapから取り除く。
fn add_coefficient(
    coefficients: &mut BTreeMap<Fact, Scalar>,
    fact: &Fact,
    coefficient: Scalar,
    control: &Control,
) -> Result<(), ValidationFailure> {
    tick(control)?;
    #[cfg(test)]
    observe(TestPoint::Coefficient);
    controlled(control, || {
        let value = match coefficients.get(fact) {
            Some(previous) => numeric::binary(BinOp::Add, previous, &coefficient, control)?,
            None => coefficient,
        };
        tick(control)?;
        if is_zero(&value)? {
            coefficients.remove(fact);
        } else {
            coefficients.insert(fact.clone(), value);
        }
        tick(control)?;
        Ok(())
    })
}

pub(crate) fn unary(
    op: UnOp,
    form: Option<&Form>,
    control: &Control,
) -> Result<Option<Form>, ValidationFailure> {
    controlled(control, || {
        let Some(form) = form else {
            return Ok(None);
        };
        form.check(control)?;
        if op != UnOp::Neg {
            return Ok(None);
        }
        let constant = numeric::unary(op, &form.constant, control)?;
        let mut coefficients = BTreeMap::new();
        for (fact, coefficient) in &form.coefficients {
            tick(control)?;
            let coefficient = numeric::unary(op, coefficient, control)?;
            add_coefficient(&mut coefficients, fact, coefficient, control)?;
            tick(control)?;
        }
        Ok(Some(Form {
            ty: form.ty.clone(),
            constant,
            coefficients,
        }))
    })
}

fn scale(form: &Form, factor: &Scalar, control: &Control) -> Result<Form, ValidationFailure> {
    controlled(control, || {
        let constant = numeric::binary(BinOp::Mul, &form.constant, factor, control)?;
        let mut coefficients = BTreeMap::new();
        for (fact, coefficient) in &form.coefficients {
            tick(control)?;
            let coefficient = numeric::binary(BinOp::Mul, coefficient, factor, control)?;
            add_coefficient(&mut coefficients, fact, coefficient, control)?;
            tick(control)?;
        }
        Ok(Form {
            ty: form.ty.clone(),
            constant,
            coefficients,
        })
    })
}

pub(crate) fn binary(
    op: BinOp,
    left: Option<&Form>,
    right: Option<&Form>,
    control: &Control,
) -> Result<Option<Form>, ValidationFailure> {
    controlled(control, || {
        let (Some(left), Some(right)) = (left, right) else {
            return Ok(None);
        };
        left.check(control)?;
        right.check(control)?;
        if left.ty != right.ty {
            return Err("アフィン演算の左右の型が異なる".into());
        }
        if op == BinOp::Mul {
            return if left.coefficients.is_empty() {
                Ok(Some(scale(right, &left.constant, control)?))
            } else if right.coefficients.is_empty() {
                Ok(Some(scale(left, &right.constant, control)?))
            } else {
                Ok(None)
            };
        }
        if !matches!(op, BinOp::Add | BinOp::Sub) {
            return Ok(None);
        }
        let constant = numeric::binary(op, &left.constant, &right.constant, control)?;
        let mut coefficients = BTreeMap::new();
        for (fact, coefficient) in &left.coefficients {
            tick(control)?;
            add_coefficient(&mut coefficients, fact, coefficient.clone(), control)?;
            tick(control)?;
        }
        for (fact, coefficient) in &right.coefficients {
            tick(control)?;
            let coefficient = if op == BinOp::Sub {
                numeric::unary(UnOp::Neg, coefficient, control)?
            } else {
                coefficient.clone()
            };
            add_coefficient(&mut coefficients, fact, coefficient, control)?;
            tick(control)?;
        }
        Ok(Some(Form {
            ty: left.ty.clone(),
            constant,
            coefficients,
        }))
    })
}

/// 元の左右は未知のまま、差が全補完で定数となるEq/Neだけを判断する。
pub(crate) fn equality(
    op: BinOp,
    left: Option<&Form>,
    right: Option<&Form>,
    control: &Control,
) -> Result<Option<(Scalar, Scalar)>, ValidationFailure> {
    controlled(control, || {
        if !matches!(op, BinOp::Eq | BinOp::Ne) {
            return Ok(None);
        }
        let Some(difference) = binary(BinOp::Sub, left, right, control)? else {
            return Ok(None);
        };
        let Some(residual) = difference.value(control)? else {
            return Ok(None);
        };
        let zero = numeric::zero(&difference.ty, control)?;
        let value = numeric::binary(op, &residual, &zero, control)?;
        Ok(Some((value, residual)))
    })
}

/// 正規化の実処理を固定点で中断する試験専用通知。時間・RSSは測定しない。
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TestPoint {
    Coefficient,
    Constant,
}

#[cfg(test)]
type Observer = Box<dyn FnMut(TestPoint)>;

#[cfg(test)]
thread_local! {
    static OBSERVER: std::cell::RefCell<Option<Observer>> = const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
fn observe(point: TestPoint) {
    OBSERVER.with(|observer| {
        if let Some(observer) = observer.borrow_mut().as_mut() {
            observer(point);
        }
    });
}

#[cfg(test)]
pub(crate) fn with_observer<T>(
    observer: impl FnMut(TestPoint) + 'static,
    work: impl FnOnce() -> T,
) -> T {
    struct Restore(Option<Observer>);
    impl Drop for Restore {
        fn drop(&mut self) {
            OBSERVER.with(|observer| *observer.borrow_mut() = self.0.take());
        }
    }
    let previous = OBSERVER.with(|slot| slot.borrow_mut().replace(Box::new(observer)));
    let _restore = Restore(previous);
    work()
}
