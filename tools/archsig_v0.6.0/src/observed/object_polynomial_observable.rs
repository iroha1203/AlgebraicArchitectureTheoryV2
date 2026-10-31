//! 元の共有K[X]を保つ有限block積と、base root存在Atom上の方程式座標。
use crate::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
};
use super::{
    equation_polynomial::{EquationPolynomial, invalid},
    numeric,
    object_equation_presentation::{
        EquationPresentation, EquationPresentationFailure, EquationPresentationStatus as Status,
        EquationRing, object_equation_presentation,
    },
};
use crate::{
    construction::{ConstructionFailure, FactPointer, readings::ObjectEvaluationPosition},
    law::ast::BinOp,
};
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::PolynomialObservable)
        .map_err(Into::into)
}
fn bad(s: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(s.into())
}
fn selection(s: &str) -> ConstructionFailure {
    ConstructionFailure::InvalidSelection(s.into())
}
/// この構成が生成した積要素。各blockは元の同じ共有K[X]に属する。
#[derive(Clone, Debug)]
pub struct PolynomialObservableValue {
    owner: Arc<()>,
    blocks: Vec<EquationPolynomial>,
}
impl PolynomialObservableValue {
    pub fn blocks(&self) -> &[EquationPolynomial] {
        &self.blocks
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolynomialObservableReading {
    Nu,
    Epsilon,
    Residual,
}
#[derive(Clone, Debug)]
pub struct PolynomialObservableCoordinate {
    pub occurrence: usize,
    pub position: ObjectEvaluationPosition,
    pub row: Option<usize>,
    pub case: usize,
    pub component: Vec<usize>,
    pub factor: Option<usize>,
    pub nu: Option<PolynomialObservableValue>,
    pub epsilon: Option<PolynomialObservableValue>,
    pub residual: Option<PolynomialObservableValue>,
    pub conditional_holds: Option<bool>,
    pub status: Status,
}
#[derive(Debug)]
pub struct ObjectPolynomialObservable {
    base: EquationPresentation,
    owner: Arc<()>,
    root_atom: Option<usize>,
    coordinates: Vec<PolynomialObservableCoordinate>,
    complete: bool,
}
impl ObjectPolynomialObservable {
    pub fn base(&self) -> &EquationPresentation {
        &self.base
    }
    pub fn factors(&self) -> &[EquationRing] {
        self.base.rings()
    }
    /// 単一global contextの全U。local診断のcoverへ追加しない。
    pub fn global_context(&self) -> &[FactPointer] {
        self.base.base().base().readings().construction().universe()
    }
    pub fn root_atom(&self) -> Option<usize> {
        self.root_atom
    }
    pub fn coordinates(&self) -> &[PolynomialObservableCoordinate] {
        &self.coordinates
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    pub fn status(&self) -> Status {
        if self.base.status() == Status::UnsupportedAlgorithm {
            Status::UnsupportedAlgorithm
        } else if !self.complete {
            Status::Undetermined
        } else {
            self.base.status()
        }
    }
    fn constant(
        &self,
        one: bool,
        c: &mut Control,
    ) -> Result<PolynomialObservableValue, ConstructionFailure> {
        let mut blocks = vec![];
        for factor in self.factors() {
            tick(c)?;
            let value = if one {
                numeric::literal("1", &factor.ty, c).map_err(invalid)?
            } else {
                numeric::zero(&factor.ty, c).map_err(invalid)?
            };
            blocks.push(EquationPolynomial::constant(value, c)?);
        }
        tick(c)?;
        Ok(PolynomialObservableValue {
            owner: Arc::clone(&self.owner),
            blocks,
        })
    }
    pub fn zero(&self, c: &mut Control) -> Result<PolynomialObservableValue, ConstructionFailure> {
        self.constant(false, c)
    }
    pub fn one(&self, c: &mut Control) -> Result<PolynomialObservableValue, ConstructionFailure> {
        self.constant(true, c)
    }
    fn member(
        &self,
        value: &PolynomialObservableValue,
        c: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        tick(c)?;
        if !Arc::ptr_eq(&self.owner, &value.owner) {
            return Err(selection("別のObservable構成の要素である"));
        }
        if value.blocks.len() != self.factors().len() {
            return Err(bad("Observableのfactor数が違う"));
        }
        for (block, factor) in value.blocks.iter().zip(self.factors()) {
            tick(c)?;
            if block.ty != factor.ty {
                return Err(bad("Observableのfactor型が違う"));
            }
            let zero = numeric::zero(&factor.ty, c).map_err(invalid)?;
            let mut previous: Option<&[usize]> = None;
            for term in &block.terms {
                tick(c)?;
                if term.coefficient.ty() != factor.ty || term.coefficient.scalar() == &zero {
                    return Err(bad("Observableの係数型または零項が違う"));
                }
                if previous.is_some_and(|v| v >= term.variables.as_slice()) {
                    return Err(bad("Observableの単項式順が違う"));
                }
                previous = Some(&term.variables);
                let mut last = None;
                for &index in &term.variables {
                    tick(c)?;
                    if index >= factor.symbols.len() || last.is_some_and(|v| v > index) {
                        return Err(bad("Observableの記号位置が違う"));
                    }
                    last = Some(index);
                }
            }
        }
        tick(c)
    }
    fn binary(
        &self,
        a: &PolynomialObservableValue,
        b: &PolynomialObservableValue,
        op: BinOp,
        c: &mut Control,
    ) -> Result<PolynomialObservableValue, ConstructionFailure> {
        self.member(a, c)?;
        self.member(b, c)?;
        let mut blocks = vec![];
        for (a, b) in a.blocks.iter().zip(&b.blocks) {
            tick(c)?;
            blocks.push(a.binary(op, b, c)?);
        }
        tick(c)?;
        Ok(PolynomialObservableValue {
            owner: Arc::clone(&self.owner),
            blocks,
        })
    }
    pub fn add(
        &self,
        a: &PolynomialObservableValue,
        b: &PolynomialObservableValue,
        c: &mut Control,
    ) -> Result<PolynomialObservableValue, ConstructionFailure> {
        self.binary(a, b, BinOp::Add, c)
    }
    pub fn sub(
        &self,
        a: &PolynomialObservableValue,
        b: &PolynomialObservableValue,
        c: &mut Control,
    ) -> Result<PolynomialObservableValue, ConstructionFailure> {
        self.binary(a, b, BinOp::Sub, c)
    }
    pub fn mul(
        &self,
        a: &PolynomialObservableValue,
        b: &PolynomialObservableValue,
        c: &mut Control,
    ) -> Result<PolynomialObservableValue, ConstructionFailure> {
        self.binary(a, b, BinOp::Mul, c)
    }
    pub fn is_zero(
        &self,
        value: &PolynomialObservableValue,
        c: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        self.member(value, c)?;
        for block in &value.blocks {
            tick(c)?;
            if !block.terms.is_empty() {
                return Ok(false);
            }
        }
        Ok(true)
    }
    pub fn equal(
        &self,
        a: &PolynomialObservableValue,
        b: &PolynomialObservableValue,
        c: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        let difference = self.sub(a, b, c)?;
        self.is_zero(&difference, c)
    }
    // 一つのfactorへの座標配置。単位的環準同型として扱わない。
    fn place(
        &self,
        factor: Option<usize>,
        polynomial: Option<&EquationPolynomial>,
        c: &mut Control,
    ) -> Result<Option<PolynomialObservableValue>, ConstructionFailure> {
        tick(c)?;
        let Some(polynomial) = polynomial else {
            return Ok(None);
        };
        let index = factor.ok_or_else(|| bad("元多項式のfactorがない"))?;
        let mut value = self.zero(c)?;
        let block = value
            .blocks
            .get_mut(index)
            .ok_or_else(|| bad("元多項式のfactorが範囲外"))?;
        *block = polynomial.clone();
        self.member(&value, c)?;
        Ok(Some(value))
    }
    pub fn at(
        &self,
        coordinate: usize,
        atom: usize,
        reading: PolynomialObservableReading,
        c: &mut Control,
    ) -> Result<Option<PolynomialObservableValue>, ConstructionFailure> {
        tick(c)?;
        let q = self
            .coordinates
            .get(coordinate)
            .ok_or_else(|| selection("Observableの出現座標が範囲外"))?;
        if atom >= self.global_context().len() {
            return Err(selection("ObservableのAtomが範囲外"));
        }
        let root_atom = self
            .root_atom
            .ok_or_else(|| bad("global contextのrootが未構成"))?;
        if atom != root_atom {
            return self.zero(c).map(Some);
        }
        let value = match reading {
            PolynomialObservableReading::Nu => &q.nu,
            PolynomialObservableReading::Epsilon => &q.epsilon,
            PolynomialObservableReading::Residual => &q.residual,
        };
        value
            .as_ref()
            .map(|v| {
                self.member(v, c)?;
                Ok(v.clone())
            })
            .transpose()
    }
    pub fn holds_at(
        &self,
        coordinate: usize,
        atom: usize,
        c: &mut Control,
    ) -> Result<Option<bool>, ConstructionFailure> {
        self.at(coordinate, atom, PolynomialObservableReading::Residual, c)?
            .as_ref()
            .map(|v| self.is_zero(v, c))
            .transpose()
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<(), PolynomialObservableFailure> {
        self.base
            .recheck(Arc::clone(&inputs), c)
            .map_err(PolynomialObservableFailure::Original)?;
        let construction = self.base.base().base().readings().construction();
        let root = construction.root();
        let expected = object_polynomial_observable(
            inputs,
            construction.reading(),
            &root.snapshot,
            &root.subject,
            self.base.object(),
            c,
        )?;
        let result = (|| -> Result<(), ConstructionFailure> {
            tick(c)?;
            if self.root_atom != expected.root_atom
                || self.complete != expected.complete
                || self.coordinates.len() != expected.coordinates.len()
            {
                return Err(bad("Observableのcontext/完成状態/出現数が違う"));
            }
            for (a, b) in self.coordinates.iter().zip(&expected.coordinates) {
                tick(c)?;
                if a.occurrence != b.occurrence
                    || a.position != b.position
                    || a.row != b.row
                    || a.case != b.case
                    || a.component != b.component
                    || a.factor != b.factor
                    || a.status != b.status
                    || a.conditional_holds != b.conditional_holds
                {
                    return Err(bad("Observableの元出現/型/状態が違う"));
                }
                for (a, b) in [
                    (&a.nu, &b.nu),
                    (&a.epsilon, &b.epsilon),
                    (&a.residual, &b.residual),
                ] {
                    tick(c)?;
                    match (a, b) {
                        (None, None) => (),
                        (Some(a), Some(b)) => {
                            self.member(a, c)?;
                            expected.member(b, c)?;
                            for (a, b) in a.blocks.iter().zip(&b.blocks) {
                                tick(c)?;
                                if a != b {
                                    return Err(bad("Observableの座標値または零配置が違う"));
                                }
                            }
                        }
                        _ => return Err(bad("Observableの未評価値が違う")),
                    }
                }
            }
            tick(c)
        })();
        result.map_err(|cause| PolynomialObservableFailure::Reading {
            cause,
            partial: Box::new(expected),
        })
    }
}
#[derive(Debug)]
pub enum PolynomialObservableFailure {
    Original(EquationPresentationFailure),
    Reading {
        cause: ConstructionFailure,
        partial: Box<ObjectPolynomialObservable>,
    },
}
fn populate(
    r: &mut ObjectPolynomialObservable,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    let construction = r.base.base().base().readings().construction();
    let root = construction.root();
    let mut root_atom = None;
    for (i, atom) in construction.universe().iter().enumerate() {
        tick(c)?;
        if atom == root {
            root_atom = Some(i);
            break;
        }
    }
    r.root_atom = Some(root_atom.ok_or_else(|| bad("global contextにbase root存在Atomがない"))?);
    let count = r.base.occurrences().len();
    for (index, q) in r.base.occurrences().iter().enumerate() {
        tick(c)?;
        let nu = r.place(q.ring, q.nu.as_ref(), c)?;
        let epsilon = r.place(q.ring, q.epsilon_constant.as_ref(), c)?;
        let residual = r.place(q.ring, q.residual_constant.as_ref(), c)?;
        let conditional_holds = residual.as_ref().map(|v| r.is_zero(v, c)).transpose()?;
        let original_holds = q
            .residual
            .as_ref()
            .map(|v| {
                let zero = numeric::zero(&v.ty(), c).map_err(invalid)?;
                Ok::<_, ConstructionFailure>(v.scalar() == &zero)
            })
            .transpose()?;
        if conditional_holds != original_holds {
            return Err(bad("Observableの零性が元の条件付き残差と違う"));
        }
        r.coordinates.push(PolynomialObservableCoordinate {
            occurrence: index,
            position: q.position,
            row: q.row,
            case: q.case,
            component: q.component.clone(),
            factor: q.ring,
            nu,
            epsilon,
            residual,
            conditional_holds,
            status: q.status.clone(),
        });
        if index + 1 == count {
            r.complete = r.base.is_complete();
        }
        c.checkpoint(Checkpoint::PolynomialObservableCoordinate)
            .map_err(ConstructionFailure::from)?;
    }
    r.complete = r.base.is_complete();
    tick(c)
}
pub fn object_polynomial_observable(
    inputs: Arc<CheckedInputs>,
    reading: &str,
    snapshot: &str,
    root: &str,
    object: usize,
    c: &mut Control,
) -> Result<ObjectPolynomialObservable, PolynomialObservableFailure> {
    let base = object_equation_presentation(inputs, reading, snapshot, root, object, c)
        .map_err(PolynomialObservableFailure::Original)?;
    let mut result = ObjectPolynomialObservable {
        base,
        owner: Arc::new(()),
        root_atom: None,
        coordinates: vec![],
        complete: false,
    };
    if let Err(cause) = populate(&mut result, c) {
        return Err(PolynomialObservableFailure::Reading {
            cause,
            partial: Box::new(result),
        });
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        control::{Limits, Usage},
        input::{InputSources, check_inputs},
    };
    mod fixture {
        include!("../../tests/common/object_view_compatibility_data.rs");
    }
    fn quiet() -> Control {
        Control::new(Limits::default(), |_| Usage::default())
    }
    fn inputs(missing: bool) -> Arc<CheckedInputs> {
        let d = crate::definition::check_definitions(&[("definition0", fixture::D.as_bytes())])
            .unwrap();
        let digest = &d.vocabularies["Pattern"].digest;
        let law = format!(
            "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";view half():Q=rat(1,2);law required first(c:Part):c.quantity=0;law required rational(c:Part):half()=0;}}"
        );
        let map = if missing {
            fixture::A
                .lines()
                .filter(|l| !l.contains("\"quantity-p\""))
                .collect::<Vec<_>>()
                .join("\n")
                .replace(",\n]", "\n]")
        } else {
            fixture::A.to_string()
        };
        Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![fixture::D.as_bytes().to_vec()],
                    law.into_bytes(),
                    map.replace("@DIGEST@", digest).into_bytes(),
                ),
                &mut quiet(),
            )
            .unwrap(),
        )
    }
    fn run(i: Arc<CheckedInputs>) -> ObjectPolynomialObservable {
        object_polynomial_observable(i, "Selected", "v", "root", 0, &mut quiet()).unwrap()
    }
    #[test]
    fn recheck_rejects_forged_context_coordinates_polynomials_zero_placement_origins_and_states() {
        for mode in 0..25 {
            let i = inputs(false);
            let mut r = run(i.clone());
            let factor = r.coordinates[0].factor.unwrap();
            let other = (factor + 1) % r.factors().len();
            match mode {
                0 => r.root_atom = None,
                1 => r.root_atom = Some((r.root_atom.unwrap() + 1) % r.global_context().len()),
                2 => r.complete = false,
                3 => {
                    r.coordinates.pop();
                }
                4 => r.coordinates[0].occurrence += 1,
                5 => r.coordinates[0].position.object += 1,
                6 => r.coordinates[0].position.instance += 1,
                7 => r.coordinates[0].row = Some(999),
                8 => r.coordinates[0].case += 1,
                9 => r.coordinates[0].component.push(999),
                10 => r.coordinates[0].factor = None,
                11 => r.coordinates[0].nu = None,
                12 => r.coordinates[0].epsilon = None,
                13 => r.coordinates[0].residual = None,
                14 => r.coordinates[0].conditional_holds = Some(true),
                15 => r.coordinates[0].status = Status::Undetermined,
                16 => {
                    let value = r.one(&mut quiet()).unwrap();
                    r.coordinates[0].nu.as_mut().unwrap().blocks[factor] =
                        value.blocks[factor].clone();
                }
                17 => {
                    let value = r.one(&mut quiet()).unwrap();
                    r.coordinates[0].nu.as_mut().unwrap().blocks[other] =
                        value.blocks[other].clone();
                }
                18 => {
                    let value = r.zero(&mut quiet()).unwrap();
                    r.coordinates[0].epsilon = Some(value);
                }
                19 => r.coordinates[0].nu.as_mut().unwrap().owner = Arc::new(()),
                20 => r.coordinates[0].nu.as_mut().unwrap().blocks.clear(),
                21 => {
                    r.coordinates[0].nu.as_mut().unwrap().blocks[factor].ty =
                        crate::types::Type::Bool
                }
                22 => r.coordinates[0].residual.as_mut().unwrap().blocks[factor]
                    .terms
                    .clear(),
                23 => r.coordinates[0].nu.as_mut().unwrap().blocks[factor].terms[0]
                    .variables
                    .push(999),
                _ => r.coordinates[0]
                    .nu
                    .as_mut()
                    .unwrap()
                    .blocks
                    .swap(factor, other),
            }
            assert!(
                matches!(
                    r.recheck(i, &mut quiet()),
                    Err(PolynomialObservableFailure::Reading {
                        cause: ConstructionFailure::Inconsistent(_)
                            | ConstructionFailure::InvalidSelection(_),
                        ..
                    })
                ),
                "mode {mode}"
            );
        }
    }
    #[test]
    fn recheck_rejects_an_invented_zero_for_an_unobserved_residual() {
        let i = inputs(true);
        let mut r = run(i.clone());
        let index = r
            .coordinates
            .iter()
            .position(|q| q.residual.is_none())
            .unwrap();
        let zero = r.zero(&mut quiet()).unwrap();
        r.coordinates[index].residual = Some(zero);
        r.coordinates[index].conditional_holds = Some(true);
        assert!(matches!(
            r.recheck(i, &mut quiet()),
            Err(PolynomialObservableFailure::Reading {
                cause: ConstructionFailure::Inconsistent(_),
                ..
            })
        ));
    }
}
