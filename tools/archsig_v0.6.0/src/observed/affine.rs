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
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum NumberType {
    Z,
    Q,
}
impl NumberType {
    pub(crate) fn ty(self) -> Type {
        match self {
            Self::Z => Type::Z,
            Self::Q => Type::Q,
        }
    }
}

/// 元binderの出現と実Contextを持つ全域parameter。欠測Factとは別の記号。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Parameter {
    pub binder: (usize, usize),
    pub name: String,
    pub context: super::call::Context,
    pub kind: NumberType,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Symbol {
    Missing(MissingKey),
    Parameter(Parameter),
    // 関数外延の座標。観測slot/全称binderではなく、元引数の位置だけで対応付ける。
    TermArgument(TermArgument),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct TermArgument {
    pub argument: usize,
    pub component: Vec<usize>,
    pub kind: NumberType,
}

pub(super) enum TermDifference {
    Same,
    Different { unit: Option<TermArgument> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Form {
    ty: Type,
    constant: Scalar,
    coefficients: BTreeMap<Symbol, Scalar>,
}

/// 原始slotは一つのFactのまま保持し、数値Tupleの成分だけを内部座標に分ける。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct MissingKey {
    pub fact: Fact,
    pub component: Vec<usize>,
    pub kind: NumberType,
}
pub(crate) type MissingAssignment = Vec<(MissingKey, Scalar)>;
pub(crate) type CompletionPair = (MissingAssignment, MissingAssignment);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MissingArithmetic {
    Rational {
        solution: Vec<(MissingKey, Scalar)>,
    },
    Integer {
        gcd: Scalar,
        bezout: Vec<Scalar>,
        remainder: Scalar,
        solution: Option<Vec<(MissingKey, Scalar)>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum UniversalProof {
    Constant {
        residual: Scalar,
    },
    NonzeroParameter {
        parameter: Parameter,
        coefficient: Scalar,
        common_residual: Option<Box<Form>>,
        common_obstruction: Option<Box<MissingArithmetic>>,
    },
    Missing {
        arithmetic: MissingArithmetic,
    },
}

/// 全称Eqの係数証拠と生成した代入。意味入力として受理する型ではない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Universal {
    pub value: Option<bool>,
    pub difference: Form,
    pub parameter_coefficients: Vec<(Parameter, Scalar)>,
    pub missing_coefficients: Vec<(MissingKey, Scalar)>,
    pub proof: UniversalProof,
    pub common_counterexample: Option<Vec<(Parameter, Scalar)>>,
    pub completion_pair: Option<CompletionPair>,
}

/// 指定した内側binderだけを閉じた全称Eq。自由な外側parameterは閉じない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PartialUniversal {
    pub difference: Form,
    pub nonzero_bound: Option<(Parameter, Scalar)>,
    pub value: Option<bool>,
}

/// 全補完で偽となる共通parameter代入と、その代入後に残る算術証拠。
struct CommonCounterexample {
    parameters: Vec<(Parameter, Scalar)>,
    residual: Form,
    obstruction: Option<MissingArithmetic>,
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

fn parameter_check(parameter: &Parameter) -> Result<(), ValidationFailure> {
    if parameter.name.is_empty() || parameter.binder.0 >= parameter.binder.1 {
        return Err("アフィンparameterに元binderの名前・出現がない".into());
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
    /// 元引数・Tuple成分の辞書式順で、定数項と全係数を型付き表示する。
    pub(in crate::observed) fn term_coordinates(
        &self,
        axes: &[TermArgument],
        c: &Control,
    ) -> Result<Scalar, ValidationFailure> {
        self.check(c)?;
        for key in self.coefficients.keys() {
            tick(c)?;
            let Symbol::TermArgument(axis) = key else {
                return Err("Term正規形に別種の記号がある".into());
            };
            if !axes.contains(axis) {
                return Err("Term正規形の元引数軸がない".into());
            }
        }
        let mut items = Vec::new();
        for axis in axes {
            tick(c)?;
            items.push(
                self.coefficients
                    .get(&Symbol::TermArgument(axis.clone()))
                    .cloned()
                    .unwrap_or(numeric::zero(&self.ty, c)?),
            );
        }
        Ok(Scalar::Tuple(vec![
            self.constant.clone(),
            Scalar::List {
                element: self.ty.clone(),
                items,
            },
        ]))
    }

    pub(super) fn ty(&self, control: &Control) -> Result<Type, ValidationFailure> {
        self.check(control)?;
        Ok(self.ty.clone())
    }
    fn check(&self, control: &Control) -> Result<(), ValidationFailure> {
        controlled(control, || {
            scalar_check(&self.constant, &self.ty, control)?;
            for (symbol, coefficient) in &self.coefficients {
                tick(control)?;
                match symbol {
                    Symbol::Missing(key) => {
                        fact_check(&key.fact)?;
                        if key.kind.ty() != self.ty {
                            return Err("欠測成分の数値型が違う".into());
                        }
                    }
                    Symbol::TermArgument(argument) => {
                        if argument.kind.ty() != self.ty {
                            return Err("Term引数座標の型が係数型と違う".into());
                        }
                    }
                    Symbol::Parameter(parameter) => {
                        parameter_check(parameter)?;
                        if parameter.kind.ty() != self.ty {
                            return Err("アフィンparameterの型が係数型と違う".into());
                        }
                    }
                }
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
        coefficients.insert(
            Symbol::Missing(MissingKey {
                fact: fact.clone(),
                component: vec![],
                kind: if *ty == Type::Z {
                    NumberType::Z
                } else {
                    NumberType::Q
                },
            }),
            one,
        );
        tick(control)?;
        Ok(Some(Form {
            ty: ty.clone(),
            constant: numeric::zero(ty, control)?,
            coefficients,
        }))
    })
}

pub(crate) fn missing_component(
    ty: &Type,
    fact: &Fact,
    component: &[usize],
    control: &Control,
) -> Result<Option<Form>, ValidationFailure> {
    let Some(mut form) = missing(ty, fact, control)? else {
        return Ok(None);
    };
    let coefficients = std::mem::take(&mut form.coefficients);
    for (symbol, value) in coefficients {
        tick(control)?;
        let Symbol::Missing(mut key) = symbol else {
            return Err("成分の元記号が欠測でない".into());
        };
        key.component = component.to_vec();
        form.coefficients.insert(Symbol::Missing(key), value);
    }
    form.check(control)?;
    Ok(Some(form))
}
pub(crate) fn parameter(
    ty: &Type,
    key: &Parameter,
    control: &Control,
) -> Result<Option<Form>, ValidationFailure> {
    controlled(control, || {
        if !matches!(ty, Type::Z | Type::Q) {
            return Ok(None);
        }
        parameter_check(key)?;
        if &key.kind.ty() != ty {
            return Err("アフィンparameterの宣言型と記号型が違う".into());
        }
        let one = numeric::literal("1", ty, control)?;
        let mut coefficients = BTreeMap::new();
        tick(control)?;
        coefficients.insert(Symbol::Parameter(key.clone()), one);
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
    coefficients: &mut BTreeMap<Symbol, Scalar>,
    fact: &Symbol,
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

/// inner binderの係数だけを検査する。非零係数はその局所全称の偽を示し、
/// 全係数が消えた場合は自由なouter parameterと欠測Factの等値述語を残す。
pub(crate) fn partial_forall(
    left: Option<&Form>,
    right: Option<&Form>,
    bound: &[Parameter],
    control: &Control,
) -> Result<Option<PartialUniversal>, ValidationFailure> {
    controlled(control, || {
        let mut declared = BTreeMap::new();
        for parameter in bound {
            tick(control)?;
            parameter_check(parameter)?;
            if declared
                .insert((parameter.binder, parameter.context), parameter)
                .is_some()
            {
                return Err("部分全称の元binder・Contextが重複する".into());
            }
            tick(control)?;
        }
        for form in [left, right].into_iter().flatten() {
            form.check(control)?;
            for symbol in form.coefficients.keys() {
                tick(control)?;
                if matches!(symbol, Symbol::TermArgument(_)) {
                    return Err("Term外延座標を部分全称のbinderにできない".into());
                }
                if let Symbol::Parameter(parameter) = symbol
                    && let Some(expected) = declared.get(&(parameter.binder, parameter.context))
                    && *expected != parameter
                {
                    return Err("部分全称の元binderの名前・型が元左右の記号と違う".into());
                }
                tick(control)?;
            }
        }
        let Some(difference) = binary(BinOp::Sub, left, right, control)? else {
            return Ok(None);
        };
        let mut nonzero_bound = None;
        for (symbol, coefficient) in &difference.coefficients {
            tick(control)?;
            if let Symbol::Parameter(parameter) = symbol
                && let Some(expected) = declared.get(&(parameter.binder, parameter.context))
            {
                if *expected != parameter {
                    return Err("部分全称の元binderの名前・型が記号と違う".into());
                }
                if nonzero_bound.is_none() {
                    nonzero_bound = Some((parameter.clone(), coefficient.clone()));
                }
            }
            tick(control)?;
        }
        tick(control)?;
        #[cfg(test)]
        observe(TestPoint::PartialUniversal);
        tick(control)?;
        let value = if nonzero_bound.is_some() {
            Some(false)
        } else {
            match difference.value(control)? {
                Some(residual) => {
                    let zero = numeric::zero(&difference.ty, control)?;
                    match numeric::binary(BinOp::Eq, &residual, &zero, control)? {
                        Scalar::Bool(value) => Some(value),
                        _ => return Err("部分全称の定数残差の比較がBoolでない".into()),
                    }
                }
                None => None,
            }
        };
        Ok(Some(PartialUniversal {
            difference,
            nonzero_bound,
            value,
        }))
    })
}

/// Euclidの各反復を元Controlで挟み、正のgcdと元の符号付き係数へのBezout係数を返す。
fn extended_gcd(
    a: &BigInt,
    b: &BigInt,
    control: &Control,
) -> Result<(BigInt, BigInt, BigInt), ValidationFailure> {
    controlled(control, || {
        let (mut old_r, mut r) = (a.abs(), b.abs());
        let (mut old_s, mut s) = (BigInt::one(), BigInt::zero());
        let (mut old_t, mut t) = (BigInt::zero(), BigInt::one());
        while !r.is_zero() {
            tick(control)?;
            #[cfg(test)]
            observe(TestPoint::Gcd);
            tick(control)?;
            let quotient = &old_r / &r;
            let next_r = &old_r - &quotient * &r;
            let next_s = &old_s - &quotient * &s;
            let next_t = &old_t - &quotient * &t;
            (old_r, r) = (r, next_r);
            (old_s, s) = (s, next_s);
            (old_t, t) = (t, next_t);
            tick(control)?;
        }
        if a.is_negative() {
            old_s = -old_s;
        }
        if b.is_negative() {
            old_t = -old_t;
        }
        Ok((old_r, old_s, old_t))
    })
}

fn rational_quotient(
    numerator: &Scalar,
    denominator: &Scalar,
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    controlled(control, || {
        let (Scalar::Q(an, ad), Scalar::Q(bn, bd)) = (numerator, denominator) else {
            return Err("有理解の除算がQでない".into());
        };
        if bn.is_zero() {
            return Err("有理解で零係数を除数にした".into());
        }
        let mut n = an * bd;
        let mut d = ad * bn;
        tick(control)?;
        if d.is_negative() {
            n = -n;
            d = -d;
        }
        numeric::rational(&Scalar::Z(n), &Scalar::Z(d), control)
    })
}

/// 非零欠測係数に対する一行の可解性。Zではgcd・Bezout・剰余を全て保持する。
fn missing_arithmetic(
    ty: &Type,
    constant: &Scalar,
    missing: &[(MissingKey, Scalar)],
    control: &Control,
) -> Result<MissingArithmetic, ValidationFailure> {
    controlled(control, || {
        if missing.is_empty() {
            return Err("欠測可解性に非零欠測係数がない".into());
        }
        match (ty, constant) {
            (Type::Q, Scalar::Q(_, _)) => {
                let target = numeric::unary(UnOp::Neg, constant, control)?;
                let pivot = rational_quotient(&target, &missing[0].1, control)?;
                let mut solution = Vec::new();
                for (index, (fact, _)) in missing.iter().enumerate() {
                    tick(control)?;
                    solution.push((
                        fact.clone(),
                        if index == 0 {
                            pivot.clone()
                        } else {
                            numeric::zero(ty, control)?
                        },
                    ));
                    tick(control)?;
                }
                check_missing_solution(constant, missing, &solution, true, control)?;
                Ok(MissingArithmetic::Rational { solution })
            }
            (Type::Z, Scalar::Z(c)) => {
                let mut gcd = BigInt::zero();
                let mut bezout = Vec::<BigInt>::new();
                for (_, coefficient) in missing {
                    tick(control)?;
                    let Scalar::Z(coefficient) = coefficient else {
                        return Err("Zの欠測係数がZでない".into());
                    };
                    let (next_gcd, x, y) = extended_gcd(&gcd, coefficient, control)?;
                    for previous in &mut bezout {
                        tick(control)?;
                        *previous *= &x;
                        tick(control)?;
                    }
                    bezout.push(y);
                    gcd = next_gcd;
                    tick(control)?;
                }
                if !gcd.is_positive() {
                    return Err("非零欠測係数のgcdが正でない".into());
                }
                let mut remainder = c % &gcd;
                if remainder.is_negative() {
                    remainder += &gcd;
                }
                tick(control)?;
                let solution = if remainder.is_zero() {
                    let factor = -c / &gcd;
                    let mut values = Vec::new();
                    for ((fact, _), coefficient) in missing.iter().zip(&bezout) {
                        tick(control)?;
                        values.push((fact.clone(), Scalar::Z(&factor * coefficient)));
                        tick(control)?;
                    }
                    check_missing_solution(constant, missing, &values, true, control)?;
                    Some(values)
                } else {
                    None
                };
                let mut coefficients = Vec::new();
                let mut pairing = BigInt::zero();
                for ((_, coefficient), value) in missing.iter().zip(bezout) {
                    tick(control)?;
                    let Scalar::Z(coefficient) = coefficient else {
                        return Err("Bezoutの元係数がZでない".into());
                    };
                    pairing += coefficient * &value;
                    coefficients.push(Scalar::Z(value));
                    tick(control)?;
                }
                if pairing != gcd {
                    return Err("欠測係数とBezout係数の内積がgcdでない".into());
                }
                Ok(MissingArithmetic::Integer {
                    gcd: Scalar::Z(gcd),
                    bezout: coefficients,
                    remainder: Scalar::Z(remainder),
                    solution,
                })
            }
            _ => Err("欠測可解性の宣言型と定数項がZ/Qで一致しない".into()),
        }
    })
}

fn check_missing_solution(
    constant: &Scalar,
    missing: &[(MissingKey, Scalar)],
    values: &[(MissingKey, Scalar)],
    expected_zero: bool,
    control: &Control,
) -> Result<(), ValidationFailure> {
    controlled(control, || {
        if missing.len() != values.len() {
            return Err("欠測解と元係数のslot数が違う".into());
        }
        let mut residual = constant.clone();
        for ((fact, coefficient), (assigned, value)) in missing.iter().zip(values) {
            tick(control)?;
            if fact != assigned {
                return Err("欠測解のslot順序が元係数と違う".into());
            }
            let term = numeric::binary(BinOp::Mul, coefficient, value, control)?;
            residual = numeric::binary(BinOp::Add, &residual, &term, control)?;
            tick(control)?;
        }
        if is_zero(&residual)? != expected_zero {
            return Err("生成した欠測補完の残差が指定した真偽と違う".into());
        }
        Ok(())
    })
}

fn zero_parameters(
    parameters: &[Parameter],
    control: &Control,
) -> Result<Vec<(Parameter, Scalar)>, ValidationFailure> {
    controlled(control, || {
        let mut values = Vec::new();
        for parameter in parameters {
            tick(control)?;
            values.push((
                parameter.clone(),
                numeric::zero(&parameter.kind.ty(), control)?,
            ));
            tick(control)?;
        }
        Ok(values)
    })
}

/// 実際の型付き代入だけを元parameter記号へ適用する。
/// 未指定parameterと欠測Factは元のidentity・係数のまま保持する。
pub(crate) fn substitute_parameters(
    form: &Form,
    values: &[(Parameter, Scalar)],
    control: &Control,
) -> Result<Form, ValidationFailure> {
    controlled(control, || {
        form.check(control)?;
        let mut assignments = BTreeMap::new();
        for (parameter, value) in values {
            tick(control)?;
            parameter_check(parameter)?;
            scalar_check(value, &parameter.kind.ty(), control)?;
            if assignments.insert(parameter, value).is_some() {
                return Err("parameterの具体代入が重複する".into());
            }
            tick(control)?;
        }
        let mut result = Form {
            ty: form.ty.clone(),
            constant: form.constant.clone(),
            coefficients: BTreeMap::new(),
        };
        for (symbol, coefficient) in &form.coefficients {
            tick(control)?;
            match symbol {
                Symbol::Missing(_) | Symbol::TermArgument(_) => {
                    add_coefficient(
                        &mut result.coefficients,
                        symbol,
                        coefficient.clone(),
                        control,
                    )?;
                }
                Symbol::Parameter(parameter) => {
                    if let Some(value) = assignments.get(parameter) {
                        let term = numeric::binary(BinOp::Mul, coefficient, value, control)?;
                        result.constant =
                            numeric::binary(BinOp::Add, &result.constant, &term, control)?;
                    } else {
                        add_coefficient(
                            &mut result.coefficients,
                            symbol,
                            coefficient.clone(),
                            control,
                        )?;
                    }
                }
            }
            tick(control)?;
        }
        result.check(control)?;
        Ok(result)
    })
}

/// 零と各単位で係数を検算し、全欠測補完で偽となる具体parameter代入を選ぶ。
/// 全域を有限標本で置き換える列挙ではなく、Zの合同条件の係数証拠である。
fn common_counterexample(
    difference: &Form,
    parameters: &[Parameter],
    active: &[(Parameter, Scalar)],
    missing: &[(MissingKey, Scalar)],
    control: &Control,
) -> Result<Option<CommonCounterexample>, ValidationFailure> {
    controlled(control, || {
        for index in 0..=active.len() {
            tick(control)?;
            let mut values = zero_parameters(parameters, control)?;
            if index != 0 {
                let key = &active[index - 1].0;
                let mut found = false;
                for (parameter, value) in &mut values {
                    tick(control)?;
                    if parameter == key {
                        *value = numeric::literal("1", &key.kind.ty(), control)?;
                        found = true;
                    }
                    tick(control)?;
                }
                if !found {
                    return Err("非零係数のparameterが元全域binder列にない".into());
                }
            }
            let residual = substitute_parameters(difference, &values, control)?;
            if missing.is_empty() {
                if !is_zero(&residual.constant)? {
                    return Ok(Some(CommonCounterexample {
                        parameters: values,
                        residual,
                        obstruction: None,
                    }));
                }
            } else {
                let arithmetic =
                    missing_arithmetic(&difference.ty, &residual.constant, missing, control)?;
                if matches!(
                    &arithmetic,
                    MissingArithmetic::Integer { solution: None, .. }
                ) {
                    return Ok(Some(CommonCounterexample {
                        parameters: values,
                        residual,
                        obstruction: Some(arithmetic),
                    }));
                }
            }
            tick(control)?;
        }
        Ok(None)
    })
}

/// 全称Eqを全補完で分類する。非零parameter係数は全域上の非恒等性の証拠であり、
/// 欠測を特定値へ固定した反例ではない。Neの全称へ否定を取り違えない。
pub(crate) fn universal_equality(
    left: Option<&Form>,
    right: Option<&Form>,
    parameters: &[Parameter],
    control: &Control,
) -> Result<Option<Universal>, ValidationFailure> {
    controlled(control, || {
        let Some(difference) = binary(BinOp::Sub, left, right, control)? else {
            return Ok(None);
        };
        let mut declared = BTreeSet::new();
        for parameter in parameters {
            tick(control)?;
            parameter_check(parameter)?;
            if !declared.insert(parameter) {
                return Err("全域parameterの元binderが重複する".into());
            }
            tick(control)?;
        }
        let mut active = Vec::new();
        let mut missing = Vec::new();
        for (symbol, coefficient) in &difference.coefficients {
            tick(control)?;
            match symbol {
                Symbol::Missing(fact) => missing.push((fact.clone(), coefficient.clone())),
                Symbol::TermArgument(_) => {
                    return Err("Term外延座標を観測の全称binderにできない".into());
                }
                Symbol::Parameter(parameter) => {
                    if !declared.contains(parameter) {
                        return Err("アフィン差のparameterが元全域binder列にない".into());
                    }
                    active.push((parameter.clone(), coefficient.clone()));
                }
            }
            tick(control)?;
        }
        tick(control)?;
        #[cfg(test)]
        observe(TestPoint::Universal);
        tick(control)?;
        let (value, proof, counterexample, completion_pair) =
            if let Some((key, coefficient)) = active.first() {
                let common =
                    common_counterexample(&difference, parameters, &active, &missing, control)?;
                let (counterexample, common_residual, common_obstruction) = match common {
                    Some(common) => (
                        Some(common.parameters),
                        Some(Box::new(common.residual)),
                        common.obstruction.map(Box::new),
                    ),
                    None => (None, None, None),
                };
                (
                    Some(false),
                    UniversalProof::NonzeroParameter {
                        parameter: key.clone(),
                        coefficient: coefficient.clone(),
                        common_residual,
                        common_obstruction,
                    },
                    counterexample,
                    None,
                )
            } else if missing.is_empty() {
                let value = is_zero(&difference.constant)?;
                (
                    Some(value),
                    UniversalProof::Constant {
                        residual: difference.constant.clone(),
                    },
                    if value {
                        None
                    } else {
                        Some(zero_parameters(parameters, control)?)
                    },
                    None,
                )
            } else {
                let arithmetic =
                    missing_arithmetic(&difference.ty, &difference.constant, &missing, control)?;
                let solution = match &arithmetic {
                    MissingArithmetic::Rational { solution } => Some(solution),
                    MissingArithmetic::Integer { solution, .. } => solution.as_ref(),
                };
                match solution {
                    Some(solution) => {
                        let mut false_values = Vec::new();
                        for (index, (fact, value)) in solution.iter().enumerate() {
                            tick(control)?;
                            false_values.push((
                                fact.clone(),
                                if index == 0 {
                                    numeric::binary(
                                        BinOp::Add,
                                        value,
                                        &numeric::literal("1", &difference.ty, control)?,
                                        control,
                                    )?
                                } else {
                                    value.clone()
                                },
                            ));
                            tick(control)?;
                        }
                        check_missing_solution(
                            &difference.constant,
                            &missing,
                            &false_values,
                            false,
                            control,
                        )?;
                        (
                            None,
                            UniversalProof::Missing {
                                arithmetic: arithmetic.clone(),
                            },
                            None,
                            Some((solution.clone(), false_values)),
                        )
                    }
                    None => (
                        Some(false),
                        UniversalProof::Missing { arithmetic },
                        Some(zero_parameters(parameters, control)?),
                        None,
                    ),
                }
            };
        Ok(Some(Universal {
            value,
            difference,
            parameter_coefficients: active,
            missing_coefficients: missing,
            proof,
            common_counterexample: counterexample,
            completion_pair,
        }))
    })
}

/// 正規化の実処理を固定点で中断する試験専用通知。時間・RSSは測定しない。

/// 元Termの引数位置を独立座標にする。外側の観測missing/parameterを供給しない。
pub(super) fn term_argument(key: TermArgument, c: &Control) -> Result<Form, ValidationFailure> {
    controlled(c, || {
        let ty = key.kind.ty();
        let mut coefficients = BTreeMap::new();
        coefficients.insert(Symbol::TermArgument(key), numeric::literal("1", &ty, c)?);
        Ok(Form {
            constant: numeric::zero(&ty, c)?,
            ty,
            coefficients,
        })
    })
}

/// 異なる係数には零/単位点を返す。反例は呼出し側が両方の元bodyへ再代入する。
pub(super) fn term_difference(
    a: &Form,
    b: &Form,
    c: &Control,
) -> Result<TermDifference, ValidationFailure> {
    controlled(c, || {
        let d = binary(BinOp::Sub, Some(a), Some(b), c)?.ok_or("Term差の型が数値アフィンでない")?;
        for key in d.coefficients.keys() {
            tick(c)?;
            if !matches!(key, Symbol::TermArgument(_)) {
                return Err("Term外延比較へ観測の記号が混入した".into());
            }
        }
        if !is_zero(&d.constant)? {
            return Ok(TermDifference::Different { unit: None });
        }
        if let Some((Symbol::TermArgument(key), _)) = d.coefficients.first_key_value() {
            return Ok(TermDifference::Different {
                unit: Some(key.clone()),
            });
        }
        Ok(TermDifference::Same)
    })
}

pub(super) fn term_point(
    f: &Form,
    unit: Option<&TermArgument>,
    c: &Control,
) -> Result<Scalar, ValidationFailure> {
    controlled(c, || {
        f.check(c)?;
        let mut value = f.constant.clone();
        for (key, coefficient) in &f.coefficients {
            tick(c)?;
            let Symbol::TermArgument(key) = key else {
                return Err("Term反例点へ観測の記号が混入した".into());
            };
            if Some(key) == unit {
                value = numeric::binary(BinOp::Add, &value, coefficient, c)?;
            }
        }
        Ok(value)
    })
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TestPoint {
    Coefficient,
    Constant,
    Gcd,
    Universal,
    PartialUniversal,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::control::{Limits, Usage};

    fn control() -> Control {
        Control::new(Limits::default(), |_| Usage::default())
    }

    fn binder(kind: NumberType) -> Parameter {
        Parameter {
            binder: (1, 2),
            name: "p".into(),
            context: super::super::call::Context::default(),
            kind,
        }
    }

    fn slot(name: &str) -> Fact {
        Fact {
            snapshot: "s".into(),
            subject: "x".into(),
            field: Some(name.into()),
            atom: None,
        }
    }

    fn z(n: i64) -> Scalar {
        Scalar::Z(n.into())
    }

    fn c(value: Scalar, control: &Control) -> Form {
        constant(&value, control).unwrap().unwrap()
    }

    fn add(left: &Form, right: &Form, control: &Control) -> Form {
        binary(BinOp::Add, Some(left), Some(right), control)
            .unwrap()
            .unwrap()
    }

    fn mul(left: &Form, right: &Form, control: &Control) -> Form {
        binary(BinOp::Mul, Some(left), Some(right), control)
            .unwrap()
            .unwrap()
    }

    #[test]
    fn universal_parameter_identity_is_distinct_from_missing() {
        let control = control();
        let key = binder(NumberType::Z);
        let p = parameter(&Type::Z, &key, &control).unwrap().unwrap();
        let h = missing(&Type::Z, &slot("h"), &control).unwrap().unwrap();
        assert!(p.value(&control).unwrap().is_none());
        let same = universal_equality(Some(&p), Some(&p), &[key.clone()], &control)
            .unwrap()
            .unwrap();
        assert_eq!(same.value, Some(true));
        assert_eq!(same.difference.value(&control).unwrap(), Some(z(0)));
        let distinct = universal_equality(Some(&p), Some(&h), &[key.clone()], &control)
            .unwrap()
            .unwrap();
        assert_eq!(distinct.value, Some(false));
        assert_eq!(distinct.parameter_coefficients, vec![(key.clone(), z(1))]);
        assert_eq!(
            distinct.missing_coefficients,
            vec![(
                MissingKey {
                    fact: slot("h"),
                    component: vec![],
                    kind: NumberType::Z
                },
                z(-1)
            )]
        );
        assert!(distinct.common_counterexample.is_none());
        let mut foreign = key.clone();
        foreign.context.request = 1;
        let q = parameter(&Type::Z, &foreign, &control).unwrap().unwrap();
        let unrelated = universal_equality(Some(&p), Some(&q), &[key.clone(), foreign], &control)
            .unwrap()
            .unwrap();
        assert_eq!(unrelated.value, Some(false));
        assert_eq!(unrelated.parameter_coefficients.len(), 2);
        assert!(matches!(
            parameter(&Type::Q, &key, &control),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            universal_equality(Some(&p), Some(&h), &[], &control),
            Err(ValidationFailure::Internal(_))
        ));
    }

    #[test]
    fn parameter_substitution_preserves_missing_and_unassigned_identity() {
        let control = control();
        let p = binder(NumberType::Z);
        let mut q = p.clone();
        q.binder = (3, 4);
        q.name = "q".into();
        let p_form = parameter(&Type::Z, &p, &control).unwrap().unwrap();
        let q_form = parameter(&Type::Z, &q, &control).unwrap().unwrap();
        let h = missing(&Type::Z, &slot("h"), &control).unwrap().unwrap();
        let form = add(&add(&p_form, &q_form, &control), &h, &control);
        let first = substitute_parameters(&form, &[(p.clone(), z(7))], &control).unwrap();
        assert!(first.value(&control).unwrap().is_none());
        assert_eq!(
            substitute_parameters(&first, &[(q, z(-7))], &control).unwrap(),
            h
        );
        let mut foreign = p.clone();
        foreign.context.request = 1;
        assert_eq!(
            substitute_parameters(&form, &[(foreign, z(9))], &control).unwrap(),
            form
        );
        assert!(matches!(
            substitute_parameters(&form, &[(p.clone(), z(1)), (p.clone(), z(2))], &control),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            substitute_parameters(
                &form,
                &[(p.clone(), Scalar::Q(1.into(), 1.into()))],
                &control
            ),
            Err(ValidationFailure::Internal(_))
        ));
        let mut malformed = p;
        malformed.binder = (1, 1);
        assert!(matches!(
            substitute_parameters(&form, &[(malformed, z(0))], &control),
            Err(ValidationFailure::Internal(_))
        ));
    }

    #[test]
    fn universal_integer_completion_uses_bezout_and_divisibility() {
        let control = control();
        let h = missing(&Type::Z, &slot("h"), &control).unwrap().unwrap();
        let k = missing(&Type::Z, &slot("k"), &control).unwrap().unwrap();
        let sum = add(
            &mul(&c(z(6), &control), &h, &control),
            &mul(&c(z(10), &control), &k, &control),
            &control,
        );
        let zero = c(z(0), &control);
        let impossible = universal_equality(
            Some(&add(&sum, &c(z(3), &control), &control)),
            Some(&zero),
            &[],
            &control,
        )
        .unwrap()
        .unwrap();
        assert_eq!(impossible.value, Some(false));
        assert_eq!(impossible.common_counterexample, Some(vec![]));
        let UniversalProof::Missing {
            arithmetic:
                MissingArithmetic::Integer {
                    gcd,
                    bezout,
                    remainder,
                    solution,
                },
        } = impossible.proof
        else {
            panic!("integer proof")
        };
        assert_eq!(gcd, z(2));
        assert_eq!(remainder, z(1));
        assert!(solution.is_none());
        assert_eq!(
            numeric::binary(
                BinOp::Add,
                &numeric::binary(BinOp::Mul, &z(6), &bezout[0], &control).unwrap(),
                &numeric::binary(BinOp::Mul, &z(10), &bezout[1], &control).unwrap(),
                &control
            )
            .unwrap(),
            z(2)
        );
        let possible = universal_equality(
            Some(&add(&sum, &c(z(4), &control), &control)),
            Some(&zero),
            &[],
            &control,
        )
        .unwrap()
        .unwrap();
        assert_eq!(possible.value, None);
        let (first, second) = possible.completion_pair.unwrap();
        check_missing_solution(
            &z(4),
            &possible.missing_coefficients,
            &first,
            true,
            &control,
        )
        .unwrap();
        check_missing_solution(
            &z(4),
            &possible.missing_coefficients,
            &second,
            false,
            &control,
        )
        .unwrap();
        let large = Scalar::Z(BigInt::one() << 100usize);
        let impossible = universal_equality(
            Some(&add(
                &mul(&c(large.clone(), &control), &h, &control),
                &c(z(1), &control),
                &control,
            )),
            Some(&zero),
            &[],
            &control,
        )
        .unwrap()
        .unwrap();
        assert_eq!(impossible.value, Some(false));
        assert!(
            matches!(impossible.proof, UniversalProof::Missing { arithmetic: MissingArithmetic::Integer { gcd, remainder, solution: None, .. } } if gcd == large && remainder == z(1))
        );
    }

    #[test]
    fn universal_rational_completion_constructs_exact_solutions() {
        let control = control();
        let h = missing(&Type::Q, &slot("h"), &control).unwrap().unwrap();
        let coefficient = Scalar::Q((-2).into(), 3.into());
        let offset = Scalar::Q(5.into(), 7.into());
        let form = add(
            &mul(&c(coefficient, &control), &h, &control),
            &c(offset.clone(), &control),
            &control,
        );
        let zero = c(Scalar::Q(0.into(), 1.into()), &control);
        let outcome = universal_equality(Some(&form), Some(&zero), &[], &control)
            .unwrap()
            .unwrap();
        assert_eq!(outcome.value, None);
        let UniversalProof::Missing {
            arithmetic: MissingArithmetic::Rational { solution },
        } = &outcome.proof
        else {
            panic!("rational proof")
        };
        assert_eq!(
            solution,
            &vec![(
                MissingKey {
                    fact: slot("h"),
                    component: vec![],
                    kind: NumberType::Q
                },
                Scalar::Q(15.into(), 14.into())
            )]
        );
        let (first, second) = outcome.completion_pair.unwrap();
        check_missing_solution(
            &offset,
            &outcome.missing_coefficients,
            &first,
            true,
            &control,
        )
        .unwrap();
        check_missing_solution(
            &offset,
            &outcome.missing_coefficients,
            &second,
            false,
            &control,
        )
        .unwrap();
        for (_, value) in first.iter().chain(&second) {
            numeric::check(value, &control).unwrap();
            assert_eq!(value.ty(), Type::Q);
        }
    }

    #[test]
    fn universal_nonzero_parameters_do_not_invent_shared_witnesses() {
        let control = control();
        let key = binder(NumberType::Z);
        let p = parameter(&Type::Z, &key, &control).unwrap().unwrap();
        let h = missing(&Type::Z, &slot("h"), &control).unwrap().unwrap();
        let two = c(z(2), &control);
        let zero = c(z(0), &control);
        let form = add(&mul(&two, &h, &control), &p, &control);
        let outcome = universal_equality(Some(&form), Some(&zero), &[key.clone()], &control)
            .unwrap()
            .unwrap();
        assert_eq!(outcome.value, Some(false));
        assert_eq!(
            outcome.common_counterexample,
            Some(vec![(key.clone(), z(1))])
        );
        assert!(
            matches!(&outcome.proof, UniversalProof::NonzeroParameter { common_obstruction: Some(arithmetic), .. }
                if matches!(arithmetic.as_ref(), MissingArithmetic::Integer { gcd, remainder, solution: None, .. }
                    if *gcd == z(2) && *remainder == z(1)))
        );
        let form = add(&mul(&two, &p, &control), &h, &control);
        let outcome = universal_equality(Some(&form), Some(&zero), &[key], &control)
            .unwrap()
            .unwrap();
        assert_eq!(outcome.value, Some(false));
        assert!(outcome.common_counterexample.is_none());
        assert!(outcome.completion_pair.is_none());
        assert!(matches!(
            outcome.proof,
            UniversalProof::NonzeroParameter {
                common_residual: None,
                common_obstruction: None,
                ..
            }
        ));
        let key = binder(NumberType::Q);
        let p = parameter(&Type::Q, &key, &control).unwrap().unwrap();
        let half = c(Scalar::Q(1.into(), 2.into()), &control);
        let one = c(Scalar::Q(1.into(), 1.into()), &control);
        let lhs = add(&add(&p, &half, &control), &half, &control);
        let rhs = add(&p, &one, &control);
        assert_eq!(
            universal_equality(Some(&lhs), Some(&rhs), &[key.clone()], &control)
                .unwrap()
                .unwrap()
                .value,
            Some(true)
        );
        let rhs = add(&rhs, &one, &control);
        let false_outcome = universal_equality(Some(&lhs), Some(&rhs), &[key.clone()], &control)
            .unwrap()
            .unwrap();
        assert_eq!(false_outcome.value, Some(false));
        assert_eq!(
            false_outcome.common_counterexample,
            Some(vec![(key, Scalar::Q(0.into(), 1.into()))])
        );
    }

    #[test]
    fn partial_forall_retains_outer_parameter_predicate() {
        let control = control();
        for kind in [NumberType::Z, NumberType::Q] {
            let x = binder(kind);
            let mut y = x.clone();
            y.binder = (3, 4);
            y.name = "y".into();
            y.context.frame = Some(0);
            let x_form = parameter(&kind.ty(), &x, &control).unwrap().unwrap();
            let y_form = parameter(&kind.ty(), &y, &control).unwrap().unwrap();
            let lhs = add(&x_form, &y_form, &control);
            let local = partial_forall(Some(&lhs), Some(&y_form), &[y], &control)
                .unwrap()
                .unwrap();
            assert_eq!(local.value, None);
            assert!(local.nonzero_bound.is_none());
            assert_eq!(local.difference, x_form);
            assert!(local.difference.value(&control).unwrap().is_none());
            assert!(lhs.value(&control).unwrap().is_none());
            assert!(y_form.value(&control).unwrap().is_none());
            let residual = local.difference;
            let zero = c(numeric::zero(&kind.ty(), &control).unwrap(), &control);
            assert_eq!(residual, x_form);
            assert_eq!(
                zero.value(&control).unwrap(),
                Some(numeric::zero(&kind.ty(), &control).unwrap())
            );
            assert_eq!(
                universal_equality(Some(&residual), Some(&zero), &[x], &control)
                    .unwrap()
                    .unwrap()
                    .value,
                Some(false)
            );
        }
    }

    #[test]
    fn partial_forall_classifies_only_local_inner_coefficients() {
        let control = control();
        for kind in [NumberType::Z, NumberType::Q] {
            let x = binder(kind);
            let mut y = x.clone();
            y.binder = (3, 4);
            y.name = "y".into();
            y.context.frame = Some(0);
            let x_form = parameter(&kind.ty(), &x, &control).unwrap().unwrap();
            let y_form = parameter(&kind.ty(), &y, &control).unwrap().unwrap();
            let lhs = add(&x_form, &y_form, &control);
            let rhs = add(&y_form, &x_form, &control);
            let identity = partial_forall(Some(&lhs), Some(&rhs), &[y.clone()], &control)
                .unwrap()
                .unwrap();
            assert_eq!(identity.value, Some(true));
            assert!(identity.nonzero_bound.is_none());
            let false_local = partial_forall(Some(&lhs), Some(&x_form), &[y.clone()], &control)
                .unwrap()
                .unwrap();
            assert_eq!(false_local.value, Some(false));
            assert_eq!(
                false_local.nonzero_bound,
                Some((
                    y.clone(),
                    numeric::literal("1", &kind.ty(), &control).unwrap()
                ))
            );
            assert_eq!(false_local.difference, y_form);
            let h = missing(&kind.ty(), &slot("h"), &control).unwrap().unwrap();
            let missing_local =
                partial_forall(Some(&add(&lhs, &h, &control)), Some(&rhs), &[y], &control)
                    .unwrap()
                    .unwrap();
            assert_eq!(missing_local.value, None);
            assert!(missing_local.nonzero_bound.is_none());
            assert_eq!(missing_local.difference, h);
        }
    }

    #[test]
    fn partial_forall_distinguishes_context_and_rejects_binder_mutations() {
        let control = control();
        let mut first = binder(NumberType::Z);
        first.context.frame = Some(0);
        let mut second = first.clone();
        second.context.frame = Some(1);
        let first_form = parameter(&Type::Z, &first, &control).unwrap().unwrap();
        let second_form = parameter(&Type::Z, &second, &control).unwrap().unwrap();
        let zero = c(z(0), &control);
        let free = partial_forall(Some(&first_form), Some(&zero), &[second.clone()], &control)
            .unwrap()
            .unwrap();
        assert_eq!(free.value, None);
        assert!(free.nonzero_bound.is_none());
        assert_eq!(free.difference, first_form);
        let closed = partial_forall(Some(&second_form), Some(&zero), &[second.clone()], &control)
            .unwrap()
            .unwrap();
        assert_eq!(closed.value, Some(false));
        assert_eq!(closed.nonzero_bound, Some((second.clone(), z(1))));
        let mut wrong_type = first.clone();
        wrong_type.kind = NumberType::Q;
        assert!(matches!(
            partial_forall(Some(&first_form), Some(&zero), &[wrong_type], &control),
            Err(ValidationFailure::Internal(_))
        ));
        let mut wrong_cancelled_type = first.clone();
        wrong_cancelled_type.kind = NumberType::Q;
        assert!(matches!(
            partial_forall(
                Some(&first_form),
                Some(&first_form),
                &[wrong_cancelled_type],
                &control
            ),
            Err(ValidationFailure::Internal(_))
        ));
        let mut wrong_name = first.clone();
        wrong_name.name = "renamed".into();
        assert!(matches!(
            partial_forall(Some(&first_form), Some(&zero), &[wrong_name], &control),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            partial_forall(Some(&zero), Some(&zero), &[first.clone(), first], &control),
            Err(ValidationFailure::Internal(_))
        ));
        let mut malformed = second;
        malformed.binder = (4, 4);
        assert!(matches!(
            partial_forall(Some(&zero), Some(&zero), &[malformed], &control),
            Err(ValidationFailure::Internal(_))
        ));
    }

    #[test]
    fn partial_forall_control_preserves_free_predicate_and_freezes() {
        use crate::observed::control::{Resource, StopReason};
        use crate::result::Signal;
        use std::{cell::Cell, rc::Rc};

        let baseline = control();
        let x = binder(NumberType::Z);
        let mut y = x.clone();
        y.binder = (3, 4);
        y.name = "y".into();
        y.context.frame = Some(0);
        let x_form = parameter(&Type::Z, &x, &baseline).unwrap().unwrap();
        let y_form = parameter(&Type::Z, &y, &baseline).unwrap().unwrap();
        let lhs = add(&x_form, &y_form, &baseline);
        let bound = vec![y];
        assert_eq!(
            partial_forall(Some(&lhs), Some(&y_form), &bound, &baseline)
                .unwrap()
                .unwrap()
                .value,
            None
        );
        for mode in 0..3 {
            let ready = Rc::new(Cell::new(false));
            let calls = Rc::new(Cell::new(0usize));
            let notifications = Rc::new(Cell::new(0usize));
            let probe_ready = ready.clone();
            let probe_calls = calls.clone();
            let controlled = Control::new(
                Limits {
                    time_ms: (mode == 1).then_some(5),
                    memory_mib: (mode == 2).then_some(5),
                },
                move |_| {
                    probe_calls.set(probe_calls.get() + 1);
                    if !probe_ready.get() {
                        return Usage::default();
                    }
                    Usage {
                        signal: (mode == 0).then_some(Signal::Int),
                        elapsed_ms: if mode == 1 { 7 } else { 0 },
                        memory_mib: if mode == 2 { 7 } else { 0 },
                    }
                },
            );
            let expected = match mode {
                0 => StopReason::Cancelled(Signal::Int),
                1 => StopReason::BudgetExhausted {
                    resource: Resource::TimeMs,
                    limit: 5,
                    observed: 7,
                },
                _ => StopReason::BudgetExhausted {
                    resource: Resource::MemoryMib,
                    limit: 5,
                    observed: 7,
                },
            };
            let seen = notifications.clone();
            with_observer(
                move |point| {
                    seen.set(seen.get() + 1);
                    if point == TestPoint::PartialUniversal {
                        ready.set(true);
                    }
                },
                || {
                    assert!(
                        matches!(partial_forall(Some(&lhs), Some(&y_form), &bound, &controlled),
                    Err(ValidationFailure::Stop(reason)) if reason == expected)
                    );
                    assert_eq!(controlled.stop_reason(), Some(expected.clone()));
                    let frozen_calls = calls.get();
                    let frozen_notifications = notifications.get();
                    assert!(
                        matches!(partial_forall(Some(&lhs), Some(&y_form), &bound, &controlled),
                    Err(ValidationFailure::Stop(reason)) if reason == expected)
                    );
                    assert_eq!(calls.get(), frozen_calls);
                    assert_eq!(notifications.get(), frozen_notifications);
                },
            );
            assert_eq!(
                partial_forall(Some(&lhs), Some(&y_form), &bound, &baseline)
                    .unwrap()
                    .unwrap()
                    .difference,
                x_form
            );
        }
    }

    #[test]
    fn universal_control_freezes_at_gcd_and_proof_selection() {
        use crate::observed::control::{Resource, StopReason};
        use crate::result::Signal;
        use std::{cell::Cell, rc::Rc};

        let baseline = control();
        let h = missing(&Type::Z, &slot("h"), &baseline).unwrap().unwrap();
        let form = add(
            &mul(&c(z(2), &baseline), &h, &baseline),
            &c(z(1), &baseline),
            &baseline,
        );
        let zero = c(z(0), &baseline);
        assert_eq!(
            universal_equality(Some(&form), Some(&zero), &[], &baseline)
                .unwrap()
                .unwrap()
                .value,
            Some(false)
        );
        for point in [TestPoint::Gcd, TestPoint::Universal] {
            for mode in 0..3 {
                let ready = Rc::new(Cell::new(false));
                let calls = Rc::new(Cell::new(0usize));
                let notifications = Rc::new(Cell::new(0usize));
                let probe_ready = ready.clone();
                let probe_calls = calls.clone();
                let controlled = Control::new(
                    Limits {
                        time_ms: (mode == 1).then_some(5),
                        memory_mib: (mode == 2).then_some(5),
                    },
                    move |_| {
                        probe_calls.set(probe_calls.get() + 1);
                        if !probe_ready.get() {
                            return Usage::default();
                        }
                        Usage {
                            signal: (mode == 0).then_some(Signal::Int),
                            elapsed_ms: if mode == 1 { 7 } else { 0 },
                            memory_mib: if mode == 2 { 7 } else { 0 },
                        }
                    },
                );
                let expected = match mode {
                    0 => StopReason::Cancelled(Signal::Int),
                    1 => StopReason::BudgetExhausted {
                        resource: Resource::TimeMs,
                        limit: 5,
                        observed: 7,
                    },
                    _ => StopReason::BudgetExhausted {
                        resource: Resource::MemoryMib,
                        limit: 5,
                        observed: 7,
                    },
                };
                let seen = notifications.clone();
                with_observer(
                    move |actual| {
                        seen.set(seen.get() + 1);
                        if actual == point {
                            ready.set(true);
                        }
                    },
                    || {
                        assert!(
                            matches!(universal_equality(Some(&form), Some(&zero), &[], &controlled), Err(ValidationFailure::Stop(reason)) if reason == expected)
                        );
                        let frozen_calls = calls.get();
                        let frozen_notifications = notifications.get();
                        assert_eq!(controlled.stop_reason(), Some(expected.clone()));
                        assert!(
                            matches!(universal_equality(Some(&form), Some(&zero), &[], &controlled), Err(ValidationFailure::Stop(reason)) if reason == expected)
                        );
                        assert_eq!(calls.get(), frozen_calls);
                        assert_eq!(notifications.get(), frozen_notifications);
                    },
                );
            }
        }
    }
}
