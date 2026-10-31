//! 共有Fp記号の全代入と、元多項式の生評価・整数値非零指示関数。
use super::{
    equation_polynomial::invalid,
    finite, numeric,
    numeric_transport::NumericTransportValue,
    object_equation_presentation::{
        EquationPresentation, EquationPresentationFailure, EquationSlot,
        object_equation_presentation,
    },
};
use crate::{construction::ConstructionFailure, types::Type};
use crate::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::sync::Arc;

fn bad(s: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(s.into())
}
fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::FinitePolynomialEvaluation)
        .map_err(Into::into)
}
fn same_values(
    a: &[NumericTransportValue],
    b: &[NumericTransportValue],
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    tick(c)?;
    if a.len() != b.len() {
        return Ok(false);
    }
    for (a, b) in a.iter().zip(b) {
        tick(c)?;
        if a != b {
            return Ok(false);
        }
    }
    Ok(true)
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteEquationSymbol {
    pub ring: usize,
    pub symbol: usize,
    pub slot: EquationSlot,
    pub ty: Type,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteEquationAssignment {
    values: Vec<NumericTransportValue>,
}
impl FiniteEquationAssignment {
    pub fn values(&self) -> &[NumericTransportValue] {
        &self.values
    }
}
pub use super::finite_integer_function::FiniteIntegerFunction;
use super::finite_integer_function::FiniteIntegerRing;
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinitePolynomialTableKind {
    Evaluated,
    OutsideFinitePolynomialReading,
    MissingPolynomial,
}
#[derive(Clone, Debug)]
pub struct FinitePolynomialTable {
    pub occurrence: usize,
    pub kind: FinitePolynomialTableKind,
    /// 元の係数型の差。整数の0/1への変換で上書きしない。
    values: Option<Vec<NumericTransportValue>>,
    /// 生差の非零指示関数。guard込みのνとは区別する。
    nonzero: Option<FiniteIntegerFunction>,
}
impl FinitePolynomialTable {
    pub fn values(&self) -> Option<&[NumericTransportValue]> {
        self.values.as_deref()
    }
    pub fn nonzero(&self) -> Option<&FiniteIntegerFunction> {
        self.nonzero.as_ref()
    }
}
#[derive(Debug)]
pub struct FinitePolynomialEvaluation {
    base: EquationPresentation,
    owner: Arc<()>,
    symbols: Vec<FiniteEquationSymbol>,
    domain: Vec<FiniteEquationAssignment>,
    domain_complete: bool,
    /// 全Fp記号の観測値が揃う場合だけのD内の点。
    observed_point: Option<usize>,
    tables: Vec<FinitePolynomialTable>,
    complete: bool,
}
impl FinitePolynomialEvaluation {
    pub fn base(&self) -> &EquationPresentation {
        &self.base
    }
    pub fn symbols(&self) -> &[FiniteEquationSymbol] {
        &self.symbols
    }
    pub fn domain(&self) -> &[FiniteEquationAssignment] {
        &self.domain
    }
    pub fn domain_is_complete(&self) -> bool {
        self.domain_complete
    }
    pub fn observed_point(&self) -> Option<usize> {
        self.observed_point
    }
    pub fn tables(&self) -> &[FinitePolynomialTable] {
        &self.tables
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    fn ring(&self, c: &mut Control) -> Result<FiniteIntegerRing<'_>, ConstructionFailure> {
        tick(c)?;
        if !self.domain_complete {
            return Err(ConstructionFailure::InvalidSelection(
                "有限代入Dが未完成".into(),
            ));
        }
        Ok(FiniteIntegerRing::new(
            &self.owner,
            self.domain.len(),
            Checkpoint::FinitePolynomialEvaluation,
        ))
    }
    fn member(
        &self,
        v: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        self.ring(c)?.member(v, c)
    }
    pub fn constant(
        &self,
        value: BigInt,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.ring(c)?.constant(value, c)
    }
    pub fn zero(&self, c: &mut Control) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.ring(c)?.zero(c)
    }
    pub fn one(&self, c: &mut Control) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.ring(c)?.one(c)
    }
    pub fn basis(
        &self,
        point: usize,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.ring(c)?.basis(point, c)
    }
    pub fn add(
        &self,
        a: &FiniteIntegerFunction,
        b: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.ring(c)?.add(a, b, c)
    }
    pub fn sub(
        &self,
        a: &FiniteIntegerFunction,
        b: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.ring(c)?.sub(a, b, c)
    }
    pub fn mul(
        &self,
        a: &FiniteIntegerFunction,
        b: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ConstructionFailure> {
        self.ring(c)?.mul(a, b, c)
    }
    pub fn equal(
        &self,
        a: &FiniteIntegerFunction,
        b: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        self.ring(c)?.equal(a, b, c)
    }
    pub fn is_zero(
        &self,
        a: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        self.ring(c)?.is_zero(a, c)
    }
    pub fn at(
        &self,
        a: &FiniteIntegerFunction,
        point: usize,
        c: &mut Control,
    ) -> Result<BigInt, ConstructionFailure> {
        self.ring(c)?.at(a, point, c)
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<(), FinitePolynomialFailure> {
        self.base
            .recheck(Arc::clone(&inputs), c)
            .map_err(FinitePolynomialFailure::Original)?;
        let construction = self.base.base().base().readings().construction();
        let root = construction.root();
        let expected = finite_polynomial_evaluation(
            inputs,
            construction.reading(),
            &root.snapshot,
            &root.subject,
            self.base.object(),
            c,
        )?;
        let checked = (|| -> Result<bool, ConstructionFailure> {
            c.checkpoint(Checkpoint::FinitePolynomialRecheck)?;
            tick(c)?;
            if self.symbols.len() != expected.symbols.len()
                || self.domain_complete != expected.domain_complete
                || self.observed_point != expected.observed_point
                || self.complete != expected.complete
                || self.domain.len() != expected.domain.len()
                || self.tables.len() != expected.tables.len()
            {
                return Ok(false);
            }
            for (a, b) in self.symbols.iter().zip(&expected.symbols) {
                tick(c)?;
                if a != b {
                    return Ok(false);
                }
            }
            for (a, b) in self.domain.iter().zip(&expected.domain) {
                if !same_values(&a.values, &b.values, c)? {
                    return Ok(false);
                }
            }
            for (a, b) in self.tables.iter().zip(&expected.tables) {
                tick(c)?;
                if a.occurrence != b.occurrence || a.kind != b.kind {
                    return Ok(false);
                }
                match (&a.values, &b.values) {
                    (None, None) => {}
                    (Some(a), Some(b)) => {
                        if !same_values(a, b, c)? {
                            return Ok(false);
                        }
                    }
                    _ => return Ok(false),
                }
                match (&a.nonzero, &b.nonzero) {
                    (None, None) => {}
                    (Some(a), Some(b)) => {
                        self.member(a, c)?;
                        expected.member(b, c)?;
                        for (a, b) in a.values.iter().zip(&b.values) {
                            tick(c)?;
                            if a != b {
                                return Ok(false);
                            }
                        }
                    }
                    _ => return Ok(false),
                }
            }
            c.checkpoint(Checkpoint::FinitePolynomialRecheck)?;
            Ok(true)
        })();
        match checked {
            Ok(true) => Ok(()),
            other => Err(FinitePolynomialFailure::Reading {
                cause: other
                    .err()
                    .unwrap_or_else(|| bad("有限代入・全評価・整数指示関数が現在入力と違う")),
                partial: Box::new(expected),
            }),
        }
    }
}
#[derive(Debug)]
pub enum FinitePolynomialFailure {
    Original(EquationPresentationFailure),
    Reading {
        cause: ConstructionFailure,
        partial: Box<FinitePolynomialEvaluation>,
    },
}
impl FinitePolynomialFailure {
    pub fn partial(&self) -> Option<&FinitePolynomialEvaluation> {
        match self {
            Self::Reading { partial, .. } => Some(partial),
            _ => None,
        }
    }
}
fn populate(
    out: &mut FinitePolynomialEvaluation,
    inputs: &CheckedInputs,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    let mut choices = Vec::new();
    for (ri, ring) in out.base.rings().iter().enumerate() {
        tick(c)?;
        if !matches!(ring.ty, Type::Fp(_)) {
            continue;
        }
        for (si, symbol) in ring.symbols.iter().enumerate() {
            tick(c)?;
            let values = finite::values(
                &ring.ty,
                inputs.law(),
                c,
                &mut |_| Err("Fp全域に参照rosterはない".into()),
                &mut |_| {},
            )
            .map_err(invalid)?;
            if values.values.is_empty() {
                return Err(bad("Fpの全域が空"));
            }
            let mut domain = Vec::new();
            for value in values.values {
                tick(c)?;
                domain.push(NumericTransportValue::observed(value));
            }
            choices.push(domain);
            out.symbols.push(FiniteEquationSymbol {
                ring: ri,
                symbol: si,
                slot: symbol.slot.clone(),
                ty: ring.ty.clone(),
            });
        }
    }
    let mut indices = vec![0; choices.len()];
    loop {
        tick(c)?;
        let mut values = Vec::new();
        for (domain, index) in choices.iter().zip(&indices) {
            tick(c)?;
            values.push(domain[*index].clone());
        }
        out.domain.push(FiniteEquationAssignment { values });
        let mut more = false;
        for index in (0..indices.len()).rev() {
            tick(c)?;
            if indices[index] + 1 < choices[index].len() {
                indices[index] += 1;
                more = true;
                break;
            }
            indices[index] = 0;
        }
        if !more {
            out.domain_complete = true;
        }
        c.checkpoint(Checkpoint::FinitePolynomialPoint)?;
        if !more {
            break;
        }
    }
    let mut observation = Vec::new();
    let mut known = true;
    for symbol in &out.symbols {
        tick(c)?;
        if let Some(value) = &out.base.rings()[symbol.ring].symbols[symbol.symbol].value {
            observation.push(value.clone());
        } else {
            known = false;
        }
    }
    if known {
        for (index, point) in out.domain.iter().enumerate() {
            tick(c)?;
            if point.values == observation {
                out.observed_point = Some(index);
                break;
            }
        }
        if out.observed_point.is_none() {
            return Err(bad("元のFp観測代入が全域Dにない"));
        }
    }
    for (qi, q) in out.base.occurrences().iter().enumerate() {
        tick(c)?;
        let mut table = FinitePolynomialTable {
            occurrence: qi,
            kind: FinitePolynomialTableKind::MissingPolynomial,
            values: None,
            nonzero: None,
        };
        if !matches!(q.ty, Type::Fp(_)) {
            table.kind = FinitePolynomialTableKind::OutsideFinitePolynomialReading;
        } else if let (Some(ring), Some(nu)) = (q.ring, &q.nu) {
            let source = out
                .base
                .rings()
                .get(ring)
                .ok_or_else(|| bad("元多項式の環がない"))?;
            let zero = numeric::zero(&q.ty, c).map_err(invalid)?;
            let mut values = Vec::new();
            let mut nonzero = Vec::new();
            for point in &out.domain {
                tick(c)?;
                let mut assignment = vec![None; source.symbols.len()];
                for (index, symbol) in out.symbols.iter().enumerate() {
                    tick(c)?;
                    if symbol.ring == ring {
                        assignment[symbol.symbol] = Some(point.values[index].clone());
                    }
                }
                let value = nu
                    .evaluate(&assignment, c)?
                    .ok_or_else(|| bad("完全なFp代入で元多項式が未評価"))?;
                if value.ty() != q.ty {
                    return Err(bad("元多項式の有限評価型が違う"));
                }
                nonzero.push(if value.scalar() == &zero {
                    BigInt::zero()
                } else {
                    BigInt::one()
                });
                values.push(value);
            }
            if let Some(point) = out.observed_point {
                let actual = values
                    .get(point)
                    .ok_or_else(|| bad("元観測点の生評価がない"))?;
                if q.evaluated_nu.as_ref() != Some(actual) {
                    return Err(bad("有限全評価が元多項式の対象評価と違う"));
                }
            }
            table.kind = FinitePolynomialTableKind::Evaluated;
            table.values = Some(values);
            table.nonzero = Some(FiniteIntegerFunction {
                owner: Arc::clone(&out.owner),
                values: nonzero,
            });
        }
        out.tables.push(table);
        if qi + 1 == out.base.occurrences().len() {
            out.complete = out.base.is_complete();
        }
        c.checkpoint(Checkpoint::FinitePolynomialTable)?;
    }
    out.complete = out.base.is_complete();
    tick(c)
}
pub fn finite_polynomial_evaluation(
    inputs: Arc<CheckedInputs>,
    reading: &str,
    snapshot: &str,
    root: &str,
    object: usize,
    c: &mut Control,
) -> Result<FinitePolynomialEvaluation, FinitePolynomialFailure> {
    let base =
        object_equation_presentation(Arc::clone(&inputs), reading, snapshot, root, object, c)
            .map_err(FinitePolynomialFailure::Original)?;
    let mut out = FinitePolynomialEvaluation {
        base,
        owner: Arc::new(()),
        symbols: Vec::new(),
        domain: Vec::new(),
        domain_complete: false,
        observed_point: None,
        tables: Vec::new(),
        complete: false,
    };
    match populate(&mut out, &inputs, c) {
        Ok(()) => Ok(out),
        Err(cause) => Err(FinitePolynomialFailure::Reading {
            cause,
            partial: Box::new(out),
        }),
    }
}
