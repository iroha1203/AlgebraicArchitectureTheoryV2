//! 共有有限環の対象評価。特性関数の像でZへの準同型を保持する。
use super::*;
use crate::construction::ConstructionFailure;
use num_traits::{One, Zero};

fn step(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteLawFunction)?;
    Ok(())
}
fn ring_failure(failure: ConstructionFailure) -> ValidationFailure {
    match failure {
        ConstructionFailure::Stopped(reason) => reason.into(),
        other => internal!(format!("有限環の対象評価: {other:?}")).into(),
    }
}
pub(in crate::observed) struct FiniteLawObjectEvaluation<'a> {
    family: &'a AutomaticLawValuations,
    point: usize,
    basis_images: Vec<BigInt>,
}
impl AutomaticLawValuations {
    pub(in crate::observed) fn object_evaluation(
        &self,
        c: &Control,
    ) -> Result<Option<FiniteLawObjectEvaluation<'_>>, ValidationFailure> {
        step(c)?;
        if !self.is_complete() || !self.domain_complete() {
            return Ok(None);
        }
        let Some(point) = self.observed_point() else {
            return Ok(None);
        };
        let mut basis_images = vec![];
        for index in 0..self.domain().len() {
            step(c)?;
            basis_images.push(if index == point {
                BigInt::one()
            } else {
                BigInt::zero()
            });
        }
        let evaluation = FiniteLawObjectEvaluation {
            family: self,
            point,
            basis_images,
        };
        evaluation.check(c)?;
        Ok(Some(evaluation))
    }
}
impl FiniteLawObjectEvaluation<'_> {
    pub(in crate::observed) fn point(&self) -> usize {
        self.point
    }
    pub(in crate::observed) fn basis_images(&self) -> &[BigInt] {
        &self.basis_images
    }
    fn check(&self, c: &Control) -> Result<(), ValidationFailure> {
        step(c)?;
        if !self.family.is_complete()
            || !self.family.domain_complete()
            || self.family.observed_point() != Some(self.point)
            || self.point >= self.family.domain().len()
            || self.basis_images.len() != self.family.domain().len()
        {
            return Err(internal!("有限環の対象評価が完成した元Dの観測点に対応しない").into());
        }
        let mut unit = BigInt::zero();
        for (index, value) in self.basis_images.iter().enumerate() {
            step(c)?;
            let expected = if index == self.point {
                BigInt::one()
            } else {
                BigInt::zero()
            };
            if value != &expected {
                return Err(internal!("有限環の特性関数の像が対象点の0/1値でない").into());
            }
            unit += value;
        }
        if !unit.is_one() {
            return Err(internal!("有限環の対象評価が単位を保存しない").into());
        }
        // 一つだけ1で他は0なので像は直交冪等元で、その和は1。
        // applyはその整数線形拡張であり、点ごとの和・差・積と単位を保存する。
        step(c)
    }
    pub(in crate::observed) fn apply(
        &self,
        function: &FiniteIntegerFunction,
        c: &Control,
    ) -> Result<BigInt, ValidationFailure> {
        self.check(c)?;
        self.family
            .integer_ring(c)?
            .member(function, c)
            .map_err(ring_failure)?;
        let mut value = BigInt::zero();
        for (coefficient, image) in function.values().iter().zip(&self.basis_images) {
            step(c)?;
            value += coefficient * image;
        }
        step(c)?;
        Ok(value)
    }
    pub(in crate::observed) fn constant_image(
        &self,
        function: &FiniteIntegerFunction,
        c: &Control,
    ) -> Result<FiniteIntegerFunction, ValidationFailure> {
        let value = self.apply(function, c)?;
        self.family
            .integer_ring(c)?
            .constant(value, c)
            .map_err(ring_failure)
    }
    /// 消費先の環を外から固定し、同じ長さ・同じ値の別計算を代用しない。
    pub(in crate::observed) fn recheck(
        &self,
        family: &AutomaticLawValuations,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        step(c)?;
        if !std::ptr::eq(self.family, family) {
            return Err(internal!("対象評価が消費先の共有有限環に由来しない").into());
        }
        family.recheck(inputs, readings, c)?;
        self.check(c)
    }
}

#[cfg(test)]
mod tests;
