//! 完成した同じ有限D上の整数値関数。由来の違うDは同じ長さでも混ぜない。
use super::control::{Checkpoint, Control};
use crate::{construction::ConstructionFailure, law::ast::BinOp};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::sync::Arc;
#[derive(Clone, Debug)]
pub struct FiniteIntegerFunction {
    pub(in crate::observed) owner: Arc<()>,
    pub(in crate::observed) values: Vec<BigInt>,
}
impl FiniteIntegerFunction {
    pub fn values(&self) -> &[BigInt] {
        &self.values
    }
}
pub(in crate::observed) struct FiniteIntegerRing<'a> {
    owner: &'a Arc<()>,
    dimension: usize,
    checkpoint: Checkpoint,
}
impl<'a> FiniteIntegerRing<'a> {
    pub fn new(owner: &'a Arc<()>, dimension: usize, checkpoint: Checkpoint) -> Self {
        Self {
            owner,
            dimension,
            checkpoint,
        }
    }
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    fn tick(&self, c: &mut Control) -> Result<(), ConstructionFailure> {
        c.checkpoint(self.checkpoint).map_err(Into::into)
    }
    pub fn member(
        &self,
        f: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        self.tick(c)?;
        if !Arc::ptr_eq(self.owner, &f.owner) || f.values.len() != self.dimension {
            return Err(ConstructionFailure::InvalidSelection(
                "整数値関数がこのD上の要素でない".into(),
            ));
        }
        Ok(())
    }
    /// 核が計算した全座標だけを同じDの要素へ包む。外部入力の形式ではない。
    pub fn computed(
        &self,
        values: Vec<BigInt>,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.tick(c)?;
        if values.len() != self.dimension {
            return Err(ConstructionFailure::InvalidSelection(
                "整数値関数の座標数がDと違う".into(),
            ));
        }
        Ok(FiniteIntegerFunction {
            owner: Arc::clone(self.owner),
            values,
        })
    }
    pub fn constant(
        &self,
        value: BigInt,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.tick(c)?;
        let mut values = vec![];
        for _ in 0..self.dimension {
            self.tick(c)?;
            values.push(value.clone());
        }
        self.computed(values, c)
    }
    pub fn zero(&self, c: &mut Control) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.constant(BigInt::zero(), c)
    }
    pub fn one(&self, c: &mut Control) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.constant(BigInt::one(), c)
    }
    pub fn basis(
        &self,
        point: usize,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.tick(c)?;
        if point >= self.dimension {
            return Err(ConstructionFailure::InvalidSelection(
                "有限代入の点が範囲外".into(),
            ));
        }
        let mut f = self.zero(c)?;
        f.values[point] = BigInt::one();
        self.tick(c)?;
        Ok(f)
    }
    fn binary(
        &self,
        a: &FiniteIntegerFunction,
        b: &FiniteIntegerFunction,
        op: BinOp,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.member(a, c)?;
        self.member(b, c)?;
        let mut values = vec![];
        for (a, b) in a.values.iter().zip(&b.values) {
            self.tick(c)?;
            values.push(match op {
                BinOp::Add => a + b,
                BinOp::Sub => a - b,
                BinOp::Mul => a * b,
                _ => {
                    return Err(ConstructionFailure::Inconsistent(
                        "整数値関数の演算が加減乗でない".into(),
                    ));
                }
            });
        }
        self.computed(values, c)
    }
    pub fn add(
        &self,
        a: &FiniteIntegerFunction,
        b: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.binary(a, b, BinOp::Add, c)
    }
    pub fn sub(
        &self,
        a: &FiniteIntegerFunction,
        b: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.binary(a, b, BinOp::Sub, c)
    }
    pub fn mul(
        &self,
        a: &FiniteIntegerFunction,
        b: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.binary(a, b, BinOp::Mul, c)
    }
    pub fn equal(
        &self,
        a: &FiniteIntegerFunction,
        b: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        self.member(a, c)?;
        self.member(b, c)?;
        for (a, b) in a.values.iter().zip(&b.values) {
            self.tick(c)?;
            if a != b {
                return Ok(false);
            }
        }
        self.tick(c)?;
        Ok(true)
    }
    pub fn is_zero(
        &self,
        a: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        self.member(a, c)?;
        for a in &a.values {
            self.tick(c)?;
            if !a.is_zero() {
                return Ok(false);
            }
        }
        self.tick(c)?;
        Ok(true)
    }
    pub fn at(
        &self,
        a: &FiniteIntegerFunction,
        point: usize,
        c: &mut Control,
    ) -> Result<BigInt, ConstructionFailure> {
        self.member(a, c)?;
        a.values
            .get(point)
            .cloned()
            .ok_or_else(|| ConstructionFailure::InvalidSelection("有限代入の点が範囲外".into()))
    }
}
