//! 元の解決済み型・Data宣言からの有限全値域。観測例と有限性を混同しない。
use super::{
    control::{Checkpoint, Control},
    data,
    result::{Fact, Scalar, Scope, ValidationFailure},
};
use crate::{law::CheckedLaw, types::Type};
use num_bigint::BigInt;

#[derive(Default)]
pub(super) struct Enumeration {
    pub values: Vec<Scalar>,
    pub scope: Scope,
    pub support: Vec<Fact>,
}
type Roster<'a> = dyn FnMut(&str) -> Result<Enumeration, ValidationFailure> + 'a;

fn tick(control: &Control) -> Result<(), ValidationFailure> {
    control
        .clone()
        .checkpoint(Checkpoint::FiniteIteration)
        .map_err(ValidationFailure::Stop)
}
pub(super) fn supported(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
) -> Result<bool, ValidationFailure> {
    fn visit(
        ty: &Type,
        law: &CheckedLaw,
        control: &Control,
        active: &mut Vec<String>,
    ) -> Result<bool, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(control)?;
            match ty {
                Type::Unit | Type::Bool | Type::Fp(_) | Type::Ref(_) => Ok(true),
                Type::Tuple(types) => {
                    for ty in types {
                        if !visit(ty, law, control, active)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                Type::Option(element) | Type::Set(element) => visit(element, law, control, active),
                Type::Data(family) => {
                    if active.contains(family) {
                        return Ok(false);
                    }
                    active.push(family.clone());
                    let result = (|| {
                        for ctor in data::constructors(law, family)? {
                            tick(control)?;
                            for arg in &ctor.arguments {
                                if !visit(arg, law, control, active)? {
                                    return Ok(false);
                                }
                            }
                        }
                        Ok(true)
                    })();
                    active.pop();
                    result
                }
                _ => Ok(false),
            }
        })
    }
    visit(ty, law, control, &mut Vec::new())
}

/// visitorは実評価時だけ渡す。Source再分析・再検査は同じ列挙とControlを使うが
/// 実評価phaseを報告しない。個数やbit幅による恣意的な打切りは置かない。
pub(super) fn values(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
    roster: &mut Roster<'_>,
    visitor: &mut dyn FnMut(usize),
) -> Result<Enumeration, ValidationFailure> {
    fn emit(
        values: &mut Vec<Scalar>,
        value: Scalar,
        control: &Control,
        visitor: &mut dyn FnMut(usize),
    ) -> Result<(), ValidationFailure> {
        visitor(values.len());
        tick(control)?;
        values.push(value);
        tick(control)
    }
    fn product(
        types: &[Type],
        law: &CheckedLaw,
        control: &Control,
        roster: &mut Roster<'_>,
        dependencies: &mut Enumeration,
    ) -> Result<Vec<Vec<Scalar>>, ValidationFailure> {
        let mut rows = vec![Vec::new()];
        for ty in types {
            tick(control)?;
            let values = enumerate(ty, law, control, roster, dependencies, &mut |_| {})?;
            let mut next = Vec::new();
            for row in &rows {
                for value in &values {
                    tick(control)?;
                    let mut item = row.clone();
                    item.push(value.clone());
                    next.push(item);
                    tick(control)?;
                }
            }
            rows = next;
        }
        Ok(rows)
    }
    fn enumerate(
        ty: &Type,
        law: &CheckedLaw,
        control: &Control,
        roster: &mut Roster<'_>,
        dependencies: &mut Enumeration,
        visitor: &mut dyn FnMut(usize),
    ) -> Result<Vec<Scalar>, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(control)?;
            let values = match ty {
                Type::Ref(entity) => {
                    let family = roster(entity)?;
                    dependencies.scope.merge(&family.scope);
                    dependencies.support.extend(family.support);
                    let mut values = Vec::new();
                    for value in family.values {
                        emit(&mut values, value, control, visitor)?;
                    }
                    values
                }
                Type::Unit => {
                    let mut values = Vec::new();
                    emit(&mut values, Scalar::Unit, control, visitor)?;
                    values
                }
                Type::Bool => {
                    let mut values = Vec::new();
                    emit(&mut values, Scalar::Bool(false), control, visitor)?;
                    emit(&mut values, Scalar::Bool(true), control, visitor)?;
                    values
                }
                Type::Fp(modulus) => {
                    let prime = modulus
                        .parse::<BigInt>()
                        .map_err(|_| "有限型Fpの素数が不正")?;
                    let mut value = BigInt::from(0);
                    let mut values = Vec::new();
                    while value < prime {
                        tick(control)?;
                        emit(
                            &mut values,
                            Scalar::Fp {
                                modulus: modulus.clone(),
                                value: value.clone(),
                            },
                            control,
                            visitor,
                        )?;
                        value += 1;
                        tick(control)?;
                    }
                    values
                }
                Type::Tuple(types) => {
                    let mut values = Vec::new();
                    for row in product(types, law, control, roster, dependencies)? {
                        emit(&mut values, Scalar::Tuple(row), control, visitor)?;
                    }
                    values
                }
                Type::Option(element) => {
                    let mut values = Vec::new();
                    emit(
                        &mut values,
                        Scalar::Option {
                            element: (**element).clone(),
                            value: None,
                        },
                        control,
                        visitor,
                    )?;
                    for item in enumerate(element, law, control, roster, dependencies, &mut |_| {})?
                    {
                        tick(control)?;
                        emit(
                            &mut values,
                            Scalar::Option {
                                element: (**element).clone(),
                                value: Some(Box::new(item)),
                            },
                            control,
                            visitor,
                        )?;
                        tick(control)?;
                    }
                    values
                }
                Type::Set(element) => {
                    let mut subsets: Vec<Vec<Scalar>> = vec![Vec::new()];
                    for item in enumerate(element, law, control, roster, dependencies, &mut |_| {})?
                    {
                        tick(control)?;
                        let count = subsets.len();
                        for index in 0..count {
                            tick(control)?;
                            let mut subset = subsets[index].clone();
                            subset.push(item.clone());
                            subsets.push(subset);
                            tick(control)?;
                        }
                    }
                    let mut values = Vec::new();
                    for subset in subsets {
                        tick(control)?;
                        emit(
                            &mut values,
                            data::set((**element).clone(), &subset, control)?,
                            control,
                            visitor,
                        )?;
                    }
                    values
                }
                Type::Data(family) => {
                    let mut values = Vec::new();
                    for ctor in data::constructors(law, family)? {
                        tick(control)?;
                        for args in product(&ctor.arguments, law, control, roster, dependencies)? {
                            tick(control)?;
                            emit(
                                &mut values,
                                Scalar::Data {
                                    family: family.clone(),
                                    constructor: format!("{family}.{}", ctor.name),
                                    args,
                                },
                                control,
                                visitor,
                            )?;
                            tick(control)?;
                        }
                    }
                    values
                }
                _ => return Err("有限全域でない型を列挙した".into()),
            };
            tick(control)?;
            Ok(values)
        })
    }
    let mut enumeration = Enumeration::default();
    enumeration.values = enumerate(ty, law, control, roster, &mut enumeration, visitor)?;
    enumeration.support.sort();
    enumeration.support.dedup();
    Ok(enumeration)
}
