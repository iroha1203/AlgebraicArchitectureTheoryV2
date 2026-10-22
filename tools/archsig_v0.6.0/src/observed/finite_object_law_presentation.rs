//! 選択対象の元Law全列を、同じ共有Z^Dの表示と対象評価へ接続する。
use super::observation::{FiniteLawObservation, ObservedInteger};
use super::*;
use num_traits::Zero;

#[derive(Clone, Debug)]
pub(in crate::observed) struct FiniteObjectEquation {
    column: usize,
    instance: usize,
    component: Option<Vec<usize>>,
    ty: Type,
    required: bool,
    nu: FiniteIntegerFunction,
    epsilon: Option<BigInt>,
    constant: Option<FiniteIntegerFunction>,
}
impl FiniteObjectEquation {
    pub fn column(&self) -> usize {
        self.column
    }
    pub fn instance(&self) -> usize {
        self.instance
    }
    pub fn component(&self) -> Option<&[usize]> {
        self.component.as_deref()
    }
    pub fn ty(&self) -> &Type {
        &self.ty
    }
    pub fn required(&self) -> bool {
        self.required
    }
    pub fn nu(&self) -> &FiniteIntegerFunction {
        &self.nu
    }
    pub fn epsilon(&self) -> Option<&BigInt> {
        self.epsilon.as_ref()
    }
    pub fn constant(&self) -> Option<&FiniteIntegerFunction> {
        self.constant.as_ref()
    }
}
pub(in crate::observed) struct FiniteObjectLawPresentation<'a> {
    family: &'a AutomaticLawValuations,
    observation: FiniteLawObservation<'a>,
    object: usize,
    columns: Vec<usize>,
    equations: Vec<FiniteObjectEquation>,
    required_zero: Vec<usize>,
}
fn checkpoint(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteLawFunction)?;
    Ok(())
}
fn ring_failure(failure: crate::construction::ConstructionFailure) -> ValidationFailure {
    match failure {
        crate::construction::ConstructionFailure::Stopped(stop) => stop.into(),
        other => format!("有限方程式表示の関数: {other:?}").into(),
    }
}
fn components(
    ty: Option<&Type>,
    c: &mut Control,
) -> Result<Vec<(Option<Vec<usize>>, Type)>, ValidationFailure> {
    let Some(ty) = ty else {
        return Ok(vec![(None, Type::Bool)]);
    };
    let mut pending = vec![(vec![], ty)];
    let mut result = vec![];
    while let Some((path, ty)) = pending.pop() {
        checkpoint(c)?;
        if let Type::Tuple(items) = ty {
            for (i, ty) in items.iter().enumerate().rev() {
                checkpoint(c)?;
                let mut next = path.clone();
                next.push(i);
                pending.push((next, ty));
            }
        } else {
            result.push((Some(path), ty.clone()));
        }
    }
    Ok(result)
}
impl AutomaticLawValuations {
    pub fn object_presentation<'a>(
        &'a self,
        inputs: &'a CheckedInputs,
        object: usize,
        c: &mut Control,
    ) -> Result<Option<FiniteObjectLawPresentation<'a>>, ValidationFailure> {
        checkpoint(c)?;
        let selected = self
            .readings
            .objects()
            .get(object)
            .ok_or("有限方程式表示の対象が範囲外")?;
        if !self.is_complete() || !self.domain_complete() {
            return Ok(None);
        }
        let observation = self
            .observation(inputs, c)?
            .ok_or("有限方程式表示の元観測域が未完成")?;
        let mut columns = vec![];
        let mut equations = vec![];
        for (index, column) in self.columns().iter().enumerate() {
            checkpoint(c)?;
            if self.column_object_identity(index) != Some(selected.identity()) {
                continue;
            }
            columns.push(index);
            let instance = column
                .source_instance()
                .ok_or("有限方程式の元instanceがない")?;
            let (source, _) = self
                .instance_source(index)
                .ok_or("有限方程式の元対象列がない")?;
            if self.readings.instances().get(instance) != Some(source) {
                return Err("有限方程式の元instance位置が違う".into());
            }
            for (component, ty) in components(column.equation_type.as_ref(), c)? {
                checkpoint(c)?;
                let nu = self.integer_function(index, component.as_deref(), c)?;
                let (epsilon, constant) = match observation.evaluate(&nu, c)? {
                    ObservedInteger::Determined(value) => {
                        let constant = self
                            .integer_ring(c)?
                            .constant(value.clone(), c)
                            .map_err(ring_failure)?;
                        (Some(value), Some(constant))
                    }
                    ObservedInteger::Varying { .. } | ObservedInteger::Empty => (None, None),
                };
                equations.push(FiniteObjectEquation {
                    column: index,
                    instance,
                    component,
                    ty,
                    required: column.required(),
                    nu,
                    epsilon,
                    constant,
                });
            }
        }
        let mut required_zero = vec![];
        for point in 0..self.domain().len() {
            checkpoint(c)?;
            let mut zero = true;
            for equation in equations.iter().filter(|q| q.required) {
                checkpoint(c)?;
                zero &= equation
                    .nu
                    .values()
                    .get(point)
                    .ok_or("有限方程式のD座標がない")?
                    .is_zero();
            }
            if zero {
                required_zero.push(point);
            }
        }
        checkpoint(c)?;
        Ok(Some(FiniteObjectLawPresentation {
            family: self,
            observation,
            object,
            columns,
            equations,
            required_zero,
        }))
    }
}
impl FiniteObjectLawPresentation<'_> {
    pub fn object(&self) -> usize {
        self.object
    }
    pub fn family(&self) -> &AutomaticLawValuations {
        self.family
    }
    /// 空Tuple等式のように葉がなくても、元の全列を保持する。
    pub fn columns(&self) -> &[usize] {
        &self.columns
    }
    pub fn equations(&self) -> &[FiniteObjectEquation] {
        &self.equations
    }
    pub fn required_zero(&self) -> &[usize] {
        &self.required_zero
    }
    pub fn observation(&self) -> &FiniteLawObservation<'_> {
        &self.observation
    }
    pub fn evaluated(&self) -> bool {
        !self.observation.points().is_empty() && self.equations.iter().all(|q| q.epsilon.is_some())
    }
    pub fn recheck(
        &self,
        expected_family: &AutomaticLawValuations,
        expected_object: usize,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        checkpoint(c)?;
        if !std::ptr::eq(self.family, expected_family) || self.object != expected_object {
            return Err("有限方程式表示が消費先の族・対象と違う".into());
        }
        self.observation
            .recheck(expected_family, inputs, readings, c)?;
        let expected = expected_family
            .object_presentation(inputs, expected_object, c)?
            .ok_or("有限方程式表示の元族が未完成")?;
        if self.columns != expected.columns
            || self.required_zero != expected.required_zero
            || self.equations.len() != expected.equations.len()
        {
            return Err("有限方程式表示の全列・成分・required零座標が違う".into());
        }
        let ring = expected_family.integer_ring(c)?;
        for (a, b) in self.equations.iter().zip(&expected.equations) {
            checkpoint(c)?;
            if (
                a.column,
                a.instance,
                &a.component,
                &a.ty,
                a.required,
                &a.epsilon,
            ) != (
                b.column,
                b.instance,
                &b.component,
                &b.ty,
                b.required,
                &b.epsilon,
            ) || !ring.equal(&a.nu, &b.nu, c).map_err(ring_failure)?
            {
                return Err("有限方程式表示の元添字・型・指示関数・対象値が違う".into());
            }
            match (&a.constant, &b.constant) {
                (None, None) => (),
                (Some(a), Some(b)) if ring.equal(a, b, c).map_err(ring_failure)? => (),
                _ => return Err("有限方程式表示の対象定数像が違う".into()),
            }
        }
        checkpoint(c)
    }
}

#[cfg(test)]
#[path = "finite_object_law_presentation_tests.rs"]
mod tests;

#[path = "finite_object_law_ideal.rs"]
pub(in crate::observed) mod ideal;
