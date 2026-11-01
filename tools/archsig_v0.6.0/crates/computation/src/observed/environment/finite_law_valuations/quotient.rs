//! 元Lawの0/1関数からrequired idealの商と係数関数の分解を作る。
use super::*;
use crate::construction::ConstructionFailure;
use crate::observed::finite_integer_function::{FiniteIntegerFunction, FiniteIntegerRing};
use num_traits::{One, Zero};
fn invalid(f: ConstructionFailure) -> ValidationFailure {
    match f {
        ConstructionFailure::Stopped(s) => ValidationFailure::Stop(s),
        f => format!("有限整数値関数の構成: {f:?}").into(),
    }
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteLawQuotient)?;
    Ok(())
}
fn paths(ty: &Type, c: &Control) -> Result<Vec<Vec<usize>>, ValidationFailure> {
    let mut pending = vec![(vec![], ty)];
    let mut result = vec![];
    while let Some((path, ty)) = pending.pop() {
        tick(c)?;
        if let Type::Tuple(items) = ty {
            for (i, ty) in items.iter().enumerate().rev() {
                tick(c)?;
                let mut next = path.clone();
                next.push(i);
                pending.push((next, ty));
            }
        } else {
            result.push(path);
        }
    }
    Ok(result)
}
#[derive(Clone, Debug)]
pub(in crate::observed) struct FiniteLawGenerator {
    column: usize,
    component: Option<Vec<usize>>,
    value: FiniteIntegerFunction,
}
impl FiniteLawGenerator {
    pub fn column(&self) -> usize {
        self.column
    }
    pub fn component(&self) -> Option<&[usize]> {
        self.component.as_deref()
    }
    pub fn value(&self) -> &FiniteIntegerFunction {
        &self.value
    }
}
#[derive(Clone, Debug)]
pub(in crate::observed) struct FiniteIdealWitness {
    target: FiniteIntegerFunction,
    generators: Vec<FiniteLawGenerator>,
    coefficients: Vec<FiniteIntegerFunction>,
}
impl FiniteIdealWitness {
    pub fn generators(&self) -> &[FiniteLawGenerator] {
        &self.generators
    }
    pub fn coefficients(&self) -> &[FiniteIntegerFunction] {
        &self.coefficients
    }
}
#[derive(Clone, Debug)]
pub(in crate::observed) enum FiniteIdealMembership {
    Member(FiniteIdealWitness),
    NonMember { projection: FiniteIntegerFunction },
}
pub(in crate::observed) struct FiniteLawQuotient<'a> {
    base: &'a FiniteLawFamilyValuations,
    points: Vec<usize>,
    owner: Arc<()>,
}
impl FiniteLawFamilyValuations {
    pub fn integer_ring(&self, c: &Control) -> Result<FiniteIntegerRing<'_>, ValidationFailure> {
        c.checkpoint(Checkpoint::FiniteLawFunction)?;
        if !self.domain_complete {
            return Err("未完成Dに整数値関数環を作れない".into());
        }
        Ok(FiniteIntegerRing::new(
            &self.owner,
            self.domain.len(),
            Checkpoint::FiniteLawFunction,
        ))
    }
    /// Noneは元Law全体。Some(path)は元等式の葉成分。
    pub fn integer_function(
        &self,
        column: usize,
        component: Option<&[usize]>,
        c: &Control,
    ) -> Result<FiniteIntegerFunction, ValidationFailure> {
        let ring = self.integer_ring(c)?;
        let q = self.columns.get(column).ok_or("有限Lawの列が範囲外")?;
        if let Some(path) = component {
            let ty = q.equation_type.as_ref().ok_or("非等式に葉成分はない")?;
            if !paths(ty, c)?.iter().any(|p| p == path) {
                return Err("元等式に葉成分pathがない".into());
            }
        }
        if q.rows.len() != self.domain.len() {
            return Err("元Lawの全D評価が未完成".into());
        }
        let mut values = vec![];
        for (point, row) in q.rows.iter().enumerate() {
            c.checkpoint(Checkpoint::FiniteLawFunction)?;
            if row.point != point || row.condition_failed {
                return Err("元Lawの行または条件が未確定".into());
            }
            let value = match component {
                None => row.indicator.as_ref(),
                Some(path) => row
                    .components
                    .as_ref()
                    .and_then(|cs| cs.iter().find(|p| p.path == path))
                    .and_then(|p| p.indicator.as_ref()),
            }
            .ok_or("元Lawの指示関数が未決または非対応")?;
            if !value.is_zero() && !value.is_one() {
                return Err("元Lawの指示関数が0/1でない".into());
            }
            values.push(value.clone());
        }
        ring.computed(values, c).map_err(invalid)
    }
    pub fn required_generators(
        &self,
        c: &Control,
    ) -> Result<Vec<FiniteLawGenerator>, ValidationFailure> {
        self.integer_ring(c)?;
        let mut result = vec![];
        for (column, q) in self.columns.iter().enumerate() {
            tick(c)?;
            if !q.required() {
                continue;
            }
            let components = match &q.equation_type {
                Some(ty) => paths(ty, c)?.into_iter().map(Some).collect(),
                None => vec![None],
            };
            for component in components {
                tick(c)?;
                let value = self.integer_function(column, component.as_deref(), c)?;
                result.push(FiniteLawGenerator {
                    column,
                    component,
                    value,
                });
            }
        }
        tick(c)?;
        Ok(result)
    }
    pub fn required_quotient(
        &self,
        c: &Control,
    ) -> Result<FiniteLawQuotient<'_>, ValidationFailure> {
        tick(c)?;
        if !self.is_complete() {
            return Err("有限Law族が未完成でrequired商を作れない".into());
        }
        let zero = self
            .required_zero
            .as_ref()
            .ok_or("required零座標が未完成")?;
        let mut points = vec![];
        for &point in zero {
            tick(c)?;
            points.push(point);
        }
        let quotient = FiniteLawQuotient {
            base: self,
            points,
            owner: Arc::new(()),
        };
        quotient.check(c)?;
        Ok(quotient)
    }
}
impl FiniteLawQuotient<'_> {
    pub(super) fn belongs_to(&self, family: &FiniteLawFamilyValuations) -> bool {
        std::ptr::eq(self.base, family)
    }
    pub fn points(&self) -> &[usize] {
        &self.points
    }
    fn check(&self, c: &Control) -> Result<(), ValidationFailure> {
        tick(c)?;
        if !self.base.is_complete() || self.base.required_zero.as_ref() != Some(&self.points) {
            return Err("required商の座標が元Law族と違う".into());
        }
        let mut previous = None;
        for &p in &self.points {
            tick(c)?;
            if p >= self.base.domain.len() || previous.is_some_and(|q| q >= p) {
                return Err("required商の座標がD内の昇順でない".into());
            }
            previous = Some(p);
        }
        Ok(())
    }
    pub fn integer_ring(&self, c: &Control) -> Result<FiniteIntegerRing<'_>, ValidationFailure> {
        self.check(c)?;
        Ok(FiniteIntegerRing::new(
            &self.owner,
            self.points.len(),
            Checkpoint::FiniteLawFunction,
        ))
    }
    pub fn project(
        &self,
        f: &FiniteIntegerFunction,
        c: &Control,
    ) -> Result<FiniteIntegerFunction, ValidationFailure> {
        self.check(c)?;
        self.base.integer_ring(c)?.member(f, c).map_err(invalid)?;
        let mut values = vec![];
        for &p in &self.points {
            tick(c)?;
            values.push(f.values()[p].clone());
        }
        self.integer_ring(c)?.computed(values, c).map_err(invalid)
    }
    pub fn recheck(&self, inputs: &CheckedInputs, c: &Control) -> Result<(), ValidationFailure> {
        self.base.recheck(inputs, c).map_err(|f| f.cause)?;
        self.recheck_projection(c)
    }
    pub(super) fn recheck_projection(&self, c: &Control) -> Result<(), ValidationFailure> {
        self.check(c)?;
        let ring = self.integer_ring(c)?;
        for g in self.base.required_generators(c)? {
            let image = self.project(&g.value, c)?;
            if !ring.is_zero(&image, c).map_err(invalid)? {
                return Err("required生成元が商で零でない".into());
            }
        }
        tick(c)
    }
    pub fn ideal_membership(
        &self,
        f: &FiniteIntegerFunction,
        c: &Control,
    ) -> Result<FiniteIdealMembership, ValidationFailure> {
        self.check(c)?;
        let image = self.project(f, c)?;
        if !self.integer_ring(c)?.is_zero(&image, c).map_err(invalid)? {
            return Ok(FiniteIdealMembership::NonMember { projection: image });
        }
        let generators = self.base.required_generators(c)?;
        let ring = self.base.integer_ring(c)?;
        let mut coefficients = vec![];
        for _ in &generators {
            tick(c)?;
            coefficients.push(ring.zero(c).map_err(invalid)?);
        }
        for (point, value) in f.values().iter().enumerate() {
            tick(c)?;
            if value.is_zero() {
                continue;
            }
            let mut selected = None;
            for (i, g) in generators.iter().enumerate() {
                tick(c)?;
                if g.value.values()[point].is_one() {
                    selected = Some(i);
                    break;
                }
            }
            let selected = selected.ok_or("射影が零の関数にrequired生成元の係数を作れない")?;
            coefficients[selected].values[point] = value.clone();
        }
        let witness = FiniteIdealWitness {
            target: f.clone(),
            generators,
            coefficients,
        };
        self.verify_witness(f, &witness, c)?;
        tick(c)?;
        Ok(FiniteIdealMembership::Member(witness))
    }
    fn verify_witness(
        &self,
        f: &FiniteIntegerFunction,
        w: &FiniteIdealWitness,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        self.check(c)?;
        let ring = self.base.integer_ring(c)?;
        if !ring.equal(f, &w.target, c).map_err(invalid)? {
            return Err("ideal分解の対象関数が違う".into());
        }
        let expected = self.base.required_generators(c)?;
        if w.generators.len() != expected.len() || w.coefficients.len() != expected.len() {
            return Err("ideal分解の生成元・係数の個数が違う".into());
        }
        let mut sum = ring.zero(c).map_err(invalid)?;
        for ((g, e), a) in w.generators.iter().zip(&expected).zip(&w.coefficients) {
            tick(c)?;
            if g.column != e.column
                || g.component != e.component
                || !ring.equal(&g.value, &e.value, c).map_err(invalid)?
            {
                return Err("ideal分解の元Law生成元が違う".into());
            }
            let term = ring.mul(a, &g.value, c).map_err(invalid)?;
            sum = ring.add(&sum, &term, c).map_err(invalid)?;
        }
        if !ring.equal(&sum, f, c).map_err(invalid)? {
            return Err("ideal分解の係数関数の和が元関数と違う".into());
        }
        tick(c)
    }
    pub fn recheck_membership(
        &self,
        inputs: &CheckedInputs,
        f: &FiniteIntegerFunction,
        membership: &FiniteIdealMembership,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        self.recheck(inputs, c)?;
        self.recheck_membership_value(f, membership, c)
    }
    pub(super) fn recheck_membership_value(
        &self,
        f: &FiniteIntegerFunction,
        membership: &FiniteIdealMembership,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        match membership {
            FiniteIdealMembership::Member(w) => self.verify_witness(f, w, c),
            FiniteIdealMembership::NonMember { projection } => {
                let actual = self.project(f, c)?;
                let ring = self.integer_ring(c)?;
                if !ring.equal(&actual, projection, c).map_err(invalid)?
                    || ring.is_zero(projection, c).map_err(invalid)?
                {
                    return Err("ideal非所属の射影値が違うか零である".into());
                }
                tick(c)
            }
        }
    }
}
#[cfg(test)]
mod tests;
