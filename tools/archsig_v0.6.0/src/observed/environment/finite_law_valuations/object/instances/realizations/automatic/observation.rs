//! 既知の元原始値と両立する全Dを保持し、個別関数の一定値を検査する。
use super::*;
use crate::archmap::Slot;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum ObservedInteger {
    Determined(BigInt),
    Varying { left: usize, right: usize },
    Empty,
}
pub(in crate::observed) struct FiniteLawObservation<'a> {
    family: &'a AutomaticLawValuations,
    inputs: &'a CheckedInputs,
    known: Vec<(usize, Fact, Scalar)>,
    points: Vec<usize>,
}
fn step(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteLawFunction)?;
    Ok(())
}
fn ring_failure(failure: crate::construction::ConstructionFailure) -> ValidationFailure {
    match failure {
        crate::construction::ConstructionFailure::Stopped(stop) => stop.into(),
        other => format!("有限観測fiberの関数: {other:?}").into(),
    }
}
fn collect(
    family: &AutomaticLawValuations,
    inputs: &CheckedInputs,
    c: &mut Control,
) -> Result<(Vec<(usize, Fact, Scalar)>, Vec<usize>), ValidationFailure> {
    step(c)?;
    if &family.value.sources != inputs.sources()
        || !family.is_complete()
        || !family.domain_complete()
    {
        return Err("有限観測fiberの元入力・共有Dが違うか未完成".into());
    }
    let e = Environment::new(inputs, c)?;
    let mut known = vec![];
    for (index, position) in family.positions().iter().enumerate() {
        step(c)?;
        let field = e.field(
            &position.snapshot,
            &position.subject,
            position.field.as_deref().ok_or("有限観測の元fieldがない")?,
        )?;
        if let Slot::Known { atom, value, .. } = &field.slot {
            let value = scalar_from(value, &field.ty, inputs.law(), c)?
                .ok_or("有限観測の型付き原始値が読めない")?;
            let mut fact = position.clone();
            fact.atom = Some(atom.clone());
            known.push((index, fact, value));
        }
    }
    let mut points = vec![];
    for (index, point) in family.domain().iter().enumerate() {
        step(c)?;
        if point.len() != family.positions().len() {
            return Err("有限観測fiberの原始座標数が違う".into());
        }
        let mut matches = true;
        for (coordinate, _, value) in &known {
            step(c)?;
            matches &= data::equal(
                point.get(*coordinate).ok_or("有限観測の座標がない")?,
                value,
                c,
            )?;
        }
        if matches {
            points.push(index);
        }
    }
    if known.len() == family.positions().len()
        && (points.len() > 1 || family.observed_point() != points.first().copied())
    {
        return Err("全既知観測のfiberが元の一意観測点と違う".into());
    }
    step(c)?;
    Ok((known, points))
}
impl AutomaticLawValuations {
    pub fn observation<'a>(
        &'a self,
        inputs: &'a CheckedInputs,
        c: &mut Control,
    ) -> Result<Option<FiniteLawObservation<'a>>, ValidationFailure> {
        step(c)?;
        if &self.value.sources != inputs.sources() {
            return Err("有限観測fiberの元三入力が違う".into());
        }
        if !self.is_complete() || !self.domain_complete() {
            return Ok(None);
        }
        let (known, points) = collect(self, inputs, c)?;
        Ok(Some(FiniteLawObservation {
            family: self,
            inputs,
            known,
            points,
        }))
    }
}
impl FiniteLawObservation<'_> {
    pub fn known(&self) -> &[(usize, Fact, Scalar)] {
        &self.known
    }
    pub fn points(&self) -> &[usize] {
        &self.points
    }
    fn check(&self, c: &mut Control) -> Result<(), ValidationFailure> {
        let (known, points) = collect(self.family, self.inputs, c)?;
        if self.points != points || self.known.len() != known.len() {
            return Err("有限観測fiberの既知位置・全両立点が違う".into());
        }
        for ((i, p, v), (j, q, w)) in self.known.iter().zip(&known) {
            step(c)?;
            if i != j || p != q || !validation_identity::scalar(v, w, c)? {
                return Err("有限観測fiberの元型付き値・出典が違う".into());
            }
        }
        step(c)
    }
    /// 全環のRingMapではなく、観測fiber上で一定な個別関数だけを読む。
    pub fn evaluate(
        &self,
        function: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<ObservedInteger, ValidationFailure> {
        self.check(c)?;
        self.family
            .integer_ring(c)?
            .member(function, c)
            .map_err(ring_failure)?;
        let Some(&first) = self.points.first() else {
            return Ok(ObservedInteger::Empty);
        };
        let value = function
            .values()
            .get(first)
            .ok_or("有限観測の元関数値がない")?;
        for &point in &self.points {
            step(c)?;
            if function
                .values()
                .get(point)
                .ok_or("有限観測の関数値がない")?
                != value
            {
                step(c)?;
                return Ok(ObservedInteger::Varying {
                    left: first,
                    right: point,
                });
            }
        }
        step(c)?;
        Ok(ObservedInteger::Determined(value.clone()))
    }
    pub fn constant_image(
        &self,
        function: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<Option<FiniteIntegerFunction>, ValidationFailure> {
        match self.evaluate(function, c)? {
            ObservedInteger::Determined(value) => self
                .family
                .integer_ring(c)?
                .constant(value, c)
                .map(Some)
                .map_err(ring_failure),
            ObservedInteger::Varying { .. } | ObservedInteger::Empty => Ok(None),
        }
    }
    pub fn recheck(
        &self,
        family: &AutomaticLawValuations,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        step(c)?;
        if !std::ptr::eq(self.family, family) || self.inputs.sources() != inputs.sources() {
            return Err("有限観測fiberが消費先の族・三入力と違う".into());
        }
        family.recheck(inputs, readings, c)?;
        self.check(c)
    }
}

#[cfg(test)]
mod tests;
