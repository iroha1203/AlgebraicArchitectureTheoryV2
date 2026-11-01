//! 元成分のνからwitness idealとrequiredの和を作る。同じ環のεとは区別する。
use super::*;
use num_traits::One;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::observed) enum FiniteObjectIdealKind {
    Witness { equation: usize },
    Obstruction,
}
pub(in crate::observed) struct FiniteObjectLawIdeal<'a, 'b> {
    base: &'a FiniteObjectLawPresentation<'b>,
    kind: FiniteObjectIdealKind,
    equations: Vec<usize>,
    zero_points: Vec<usize>,
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteLawQuotient)?;
    Ok(())
}
fn construct<'a, 'b>(
    base: &'a FiniteObjectLawPresentation<'b>,
    kind: FiniteObjectIdealKind,
    c: &Control,
) -> Result<FiniteObjectLawIdeal<'a, 'b>, ValidationFailure> {
    tick(c)?;
    let mut equations = vec![];
    match kind {
        FiniteObjectIdealKind::Witness { equation } => {
            base.equations()
                .get(equation)
                .ok_or("witness idealの元成分が範囲外")?;
            equations.push(equation);
        }
        FiniteObjectIdealKind::Obstruction => {
            for (index, equation) in base.equations().iter().enumerate() {
                tick(c)?;
                if equation.required() {
                    equations.push(index);
                }
            }
        }
    }
    let ring = base.family().integer_ring(c)?;
    for &index in &equations {
        tick(c)?;
        let function = base.equations()[index].nu();
        ring.member(function, c).map_err(ring_failure)?;
        for value in function.values() {
            tick(c)?;
            if !value.is_zero() && !value.is_one() {
                return Err("有限idealの元νが0/1指示値でない".into());
            }
        }
    }
    let mut zero_points = vec![];
    for point in 0..ring.dimension() {
        tick(c)?;
        let mut zero = true;
        for &index in &equations {
            tick(c)?;
            zero &= base.equations()[index]
                .nu()
                .values()
                .get(point)
                .ok_or("有限idealの元D座標がない")?
                .is_zero();
        }
        if zero {
            zero_points.push(point);
        }
    }
    if kind == FiniteObjectIdealKind::Obstruction && zero_points != base.required_zero() {
        return Err("required idealの零座標が元表示と違う".into());
    }
    tick(c)?;
    Ok(FiniteObjectLawIdeal {
        base,
        kind,
        equations,
        zero_points,
    })
}
impl<'b> FiniteObjectLawPresentation<'b> {
    pub fn witness_ideal<'a>(
        &'a self,
        equation: usize,
        c: &Control,
    ) -> Result<FiniteObjectLawIdeal<'a, 'b>, ValidationFailure> {
        construct(self, FiniteObjectIdealKind::Witness { equation }, c)
    }
    pub fn required_ideal<'a>(
        &'a self,
        c: &Control,
    ) -> Result<FiniteObjectLawIdeal<'a, 'b>, ValidationFailure> {
        construct(self, FiniteObjectIdealKind::Obstruction, c)
    }
}
impl FiniteObjectLawIdeal<'_, '_> {
    pub fn kind(&self) -> FiniteObjectIdealKind {
        self.kind
    }
    pub fn base(&self) -> &FiniteObjectLawPresentation<'_> {
        self.base
    }
    /// 各位置は元表示のinstance/全parameter/component/roleを保持した成分を指す。
    pub fn equations(&self) -> &[usize] {
        &self.equations
    }
    pub fn zero_points(&self) -> &[usize] {
        &self.zero_points
    }
    pub fn generators(
        &self,
        c: &Control,
    ) -> Result<Vec<&FiniteIntegerFunction>, ValidationFailure> {
        self.check(c)?;
        let mut values = vec![];
        for &index in &self.equations {
            tick(c)?;
            values.push(self.base.equations()[index].nu());
        }
        tick(c)?;
        Ok(values)
    }
    fn check(&self, c: &Control) -> Result<(), ValidationFailure> {
        let expected = construct(self.base, self.kind, c)?;
        if self.equations != expected.equations || self.zero_points != expected.zero_points {
            return Err("有限idealの元生成元・全零座標が違う".into());
        }
        tick(c)
    }
    pub fn is_zero(&self, c: &Control) -> Result<bool, ValidationFailure> {
        self.check(c)?;
        // 全元νが全Dで零であること。対象におけるεの零性とは別。
        Ok(self.zero_points.len() == self.base.family().domain().len())
    }
    pub fn recheck(
        &self,
        base: &FiniteObjectLawPresentation<'_>,
        family: &AutomaticLawValuations,
        object: usize,
        kind: FiniteObjectIdealKind,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        tick(c)?;
        if !std::ptr::eq(self.base, base) || self.kind != kind {
            return Err("有限idealが消費先の表示・種別・成分と違う".into());
        }
        base.recheck(family, object, inputs, readings, c)?;
        self.check(c)
    }
}

#[cfg(test)]
mod tests;
