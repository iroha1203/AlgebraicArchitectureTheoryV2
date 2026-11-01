//! 元の解決済み型・Data宣言からの有限全値域。観測例と有限性を混同しない。
use super::{
    data,
    result::{Fact, Scalar, Scope, ValidationFailure},
};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::types::Type;
use archsig_input::law::CheckedLaw;
use num_bigint::BigInt;

#[derive(Clone, Default)]
pub(super) struct Enumeration {
    pub values: Vec<Scalar>,
    pub scope: Scope,
    pub support: Vec<Fact>,
}
#[derive(Clone, Default)]
pub(super) struct FiniteDomain {
    pub enumeration: Enumeration,
    pub missing: Vec<Fact>,
}
type OwnedDomainRoster<'a> = dyn FnMut(&str, &str) -> Result<FiniteDomain, ValidationFailure> + 'a;
type Roster<'a> = dyn FnMut(&str) -> Result<Enumeration, ValidationFailure> + 'a;
type OwnedRoster<'a> = dyn FnMut(&str, &str) -> Result<Enumeration, ValidationFailure> + 'a;

fn tick(control: &Control) -> Result<(), ValidationFailure> {
    control
        .checkpoint(Checkpoint::FiniteIteration)
        .map_err(ValidationFailure::Stop)
}
pub(super) fn supported(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
) -> Result<bool, ValidationFailure> {
    supported_with_references(ty, law, control, true, true)
}

/// 欠測fieldを入力の参照制約と独立に補完できる有限値型。
/// Dataの全constructor引数も元宣言から読み、参照を含む型を許可しない。
pub(super) fn completion_supported(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
) -> Result<bool, ValidationFailure> {
    supported_with_references(ty, law, control, false, false)
}

/// 元入力の所属・Map全域性条件へ全値をpinする有限field。
pub(super) fn field_completion_supported(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
) -> Result<bool, ValidationFailure> {
    supported_with_references(&ty.erase(), law, control, true, true)
}

fn supported_with_references(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
    references: bool,
    maps: bool,
) -> Result<bool, ValidationFailure> {
    fn visit(
        ty: &Type,
        law: &CheckedLaw,
        control: &Control,
        active: &mut Vec<String>,
        references: bool,
        maps: bool,
    ) -> Result<bool, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(control)?;
            match ty {
                Type::Unit | Type::Bool | Type::Fp(_) => Ok(true),
                Type::Ref(_) => Ok(references),
                // Map fieldの補完には入力全体の参照制約が必要。型全域の
                // 列挙だけを、元の有限参照族上の全域関数として許可する。
                // Ownedは実ownerを復元する依存経路が扱う。その入口は
                // 消去型で本判定を行い、実列挙では元Owned型を保つ。
                Type::Map(domain, codomain) => Ok(maps
                    && matches!(domain.as_ref(), Type::Ref(_))
                    && matches!(codomain.as_ref(), Type::Ref(_))),
                Type::Tuple(types) => {
                    for ty in types {
                        if !visit(ty, law, control, active, references, maps)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                Type::Option(element) | Type::Set(element) => {
                    visit(element, law, control, active, references, maps)
                }
                Type::Data(family) => {
                    if active.contains(family) {
                        return Ok(false);
                    }
                    active.push(family.clone());
                    let result = (|| {
                        for ctor in data::constructors(law, family)? {
                            tick(control)?;
                            for arg in &ctor.arguments {
                                if !visit(arg, law, control, active, references, maps)? {
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
    visit(ty, law, control, &mut Vec::new(), references, maps)
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
    values_with_owned(
        ty,
        law,
        control,
        roster,
        &mut |_, _| Err("有限全域でない型を列挙した".into()),
        visitor,
    )
}

pub(super) fn values_with_owned(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
    roster: &mut Roster<'_>,
    owned: &mut OwnedRoster<'_>,
    visitor: &mut dyn FnMut(usize),
) -> Result<Enumeration, ValidationFailure> {
    enumerate_values(ty, law, control, roster, owned, visitor, false)
}

/// fieldの元型で全域性を検査する前の候補。Mapのkey集合はownerにより変わる。
/// ここで構成した部分表は、入力制約へpinしてからだけ値DAGへ公開する。
pub(super) fn field_candidates(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
    roster: &mut Roster<'_>,
    owned: &mut OwnedRoster<'_>,
    visitor: &mut dyn FnMut(usize),
) -> Result<Enumeration, ValidationFailure> {
    enumerate_values(ty, law, control, roster, owned, visitor, true)
}

/// 原始field候補は部分Mapを含め、全域性・所属は全代入を同時に検査する。
pub(super) fn field_candidates_if_finite(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
    roster: &mut Roster<'_>,
) -> Result<Option<FiniteDomain>, ValidationFailure> {
    enumerate_values_maybe(
        ty,
        law,
        control,
        roster,
        &mut |_, _| Err("field候補に消去前のOwned型がある".into()),
        &mut |_| {},
        true,
        true,
    )
}

pub(super) fn values_if_finite_with_owned(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
    roster: &mut Roster<'_>,
    owned: &mut OwnedDomainRoster<'_>,
    visitor: &mut dyn FnMut(usize),
) -> Result<Option<FiniteDomain>, ValidationFailure> {
    enumerate_values_maybe(ty, law, control, roster, owned, visitor, false, true)
}
fn enumerate_values(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
    roster: &mut Roster<'_>,
    owned: &mut OwnedRoster<'_>,
    visitor: &mut dyn FnMut(usize),
    partial_maps: bool,
) -> Result<Enumeration, ValidationFailure> {
    let mut complete_owned = |entity: &str, owner: &str| {
        owned(entity, owner).map(|enumeration| FiniteDomain {
            enumeration,
            missing: Vec::new(),
        })
    };
    enumerate_values_maybe(
        ty,
        law,
        control,
        roster,
        &mut complete_owned,
        visitor,
        partial_maps,
        false,
    )?
    .map(|domain| domain.enumeration)
    .ok_or_else(|| "有限全域でない型を列挙した".into())
}
fn enumerate_values_maybe(
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
    roster: &mut Roster<'_>,
    owned: &mut OwnedDomainRoster<'_>,
    visitor: &mut dyn FnMut(usize),
    partial_maps: bool,
    allow_degenerate: bool,
) -> Result<Option<FiniteDomain>, ValidationFailure> {
    fn merge_domain(total: &mut FiniteDomain, domain: FiniteDomain) {
        total.enumeration.scope.merge(&domain.enumeration.scope);
        total.enumeration.support.extend(domain.enumeration.support);
        total.missing.extend(domain.missing);
    }
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
        owned: &mut OwnedDomainRoster<'_>,
        dependencies: &mut FiniteDomain,
        partial_maps: bool,
        active: &mut Vec<String>,
        allow_degenerate: bool,
    ) -> Result<Option<Vec<Vec<Scalar>>>, ValidationFailure> {
        if allow_degenerate {
            tick(control)?;
            let before = dependencies.clone();
            let mut domains = Vec::new();
            let mut empty = false;
            let mut unavailable = false;
            for ty in types {
                tick(control)?;
                let mut domain = FiniteDomain::default();
                let values = enumerate(
                    ty,
                    law,
                    control,
                    roster,
                    owned,
                    &mut domain,
                    &mut |_| {},
                    partial_maps,
                    active,
                    true,
                )?;
                match values {
                    Some(values) => {
                        if values.is_empty() && domain.missing.is_empty() {
                            *dependencies = before;
                            merge_domain(dependencies, domain);
                            return Ok(Some(Vec::new()));
                        }
                        empty |= values.is_empty();
                        domains.push(values);
                    }
                    None => {
                        unavailable = true;
                        domains.push(Vec::new());
                    }
                }
                merge_domain(dependencies, domain);
            }
            if empty {
                return Ok(Some(Vec::new()));
            }
            if unavailable {
                return Ok(None);
            }
            let mut rows = vec![Vec::new()];
            for values in domains {
                tick(control)?;
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
            return Ok(Some(rows));
        }
        let mut rows = vec![Vec::new()];
        for ty in types {
            tick(control)?;
            let Some(values) = enumerate(
                ty,
                law,
                control,
                roster,
                owned,
                dependencies,
                &mut |_| {},
                partial_maps,
                active,
                allow_degenerate,
            )?
            else {
                return Ok(None);
            };
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
        Ok(Some(rows))
    }
    fn enumerate(
        ty: &Type,
        law: &CheckedLaw,
        control: &Control,
        roster: &mut Roster<'_>,
        owned: &mut OwnedDomainRoster<'_>,
        dependencies: &mut FiniteDomain,
        visitor: &mut dyn FnMut(usize),
        partial_maps: bool,
        active: &mut Vec<String>,
        allow_degenerate: bool,
    ) -> Result<Option<Vec<Scalar>>, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(control)?;
            let values = match ty {
                Type::Ref(_) | Type::Owned(_, _) => {
                    let family = match ty {
                        Type::Ref(entity) => FiniteDomain {
                            enumeration: roster(entity)?,
                            missing: Vec::new(),
                        },
                        Type::Owned(entity, owner) => owned(entity, owner)?,
                        _ => unreachable!(),
                    };
                    dependencies
                        .enumeration
                        .scope
                        .merge(&family.enumeration.scope);
                    dependencies
                        .enumeration
                        .support
                        .extend(family.enumeration.support);
                    dependencies.missing.extend(family.missing);
                    let mut values = Vec::new();
                    for value in family.enumeration.values {
                        emit(&mut values, value, control, visitor)?;
                    }
                    values
                }
                Type::Map(domain, codomain) => {
                    let missing_before_keys = dependencies.missing.len();
                    let Some(keys) = enumerate(
                        domain,
                        law,
                        control,
                        roster,
                        owned,
                        dependencies,
                        &mut |_| {},
                        partial_maps,
                        active,
                        allow_degenerate,
                    )?
                    else {
                        return Ok(None);
                    };
                    let images = if allow_degenerate
                        && keys.is_empty()
                        && dependencies.missing.len() == missing_before_keys
                    {
                        Some(Vec::new())
                    } else {
                        enumerate(
                            codomain,
                            law,
                            control,
                            roster,
                            owned,
                            dependencies,
                            &mut |_| {},
                            partial_maps,
                            active,
                            allow_degenerate,
                        )?
                    };
                    let images = match images {
                        Some(images) => images,
                        None if keys.is_empty() => Vec::new(),
                        None => return Ok(None),
                    };
                    // 型全域では空始域は空表1個、非空始域・空値域は0個。
                    // field候補は各keyの不所属も残し、元型の全域性検査へ渡す。
                    let mut tables = vec![Vec::new()];
                    for (_key_index, key) in keys.into_iter().enumerate() {
                        #[cfg(test)]
                        if partial_maps {
                            super::data::observe_iteration("map_field_key", _key_index);
                        }
                        tick(control)?;
                        let mut next = Vec::new();
                        for table in &tables {
                            if partial_maps {
                                // このkeyが元Owned始域に属さない可能性も残す。
                                tick(control)?;
                                next.push(table.clone());
                                tick(control)?;
                            }
                            for image in &images {
                                tick(control)?;
                                let mut table = table.clone();
                                table.push((key.clone(), image.clone()));
                                next.push(table);
                                tick(control)?;
                            }
                        }
                        tables = next;
                        tick(control)?;
                    }
                    let mut values = Vec::new();
                    for (_table_index, pairs) in tables.into_iter().enumerate() {
                        #[cfg(test)]
                        if partial_maps {
                            super::data::observe_iteration("map_field_candidate", _table_index);
                        }
                        tick(control)?;
                        emit(
                            &mut values,
                            Scalar::Map {
                                domain: domain.erase(),
                                codomain: codomain.erase(),
                                pairs,
                            },
                            control,
                            visitor,
                        )?;
                        tick(control)?;
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
                    let Some(rows) = product(
                        types,
                        law,
                        control,
                        roster,
                        owned,
                        dependencies,
                        partial_maps,
                        active,
                        allow_degenerate,
                    )?
                    else {
                        return Ok(None);
                    };
                    for row in rows {
                        emit(&mut values, Scalar::Tuple(row), control, visitor)?;
                    }
                    values
                }
                Type::List(element) if allow_degenerate => {
                    let Some(items) = enumerate(
                        element,
                        law,
                        control,
                        roster,
                        owned,
                        dependencies,
                        &mut |_| {},
                        partial_maps,
                        active,
                        true,
                    )?
                    else {
                        return Ok(None);
                    };
                    if !items.is_empty() {
                        return Ok(None);
                    }
                    let mut values = Vec::new();
                    emit(
                        &mut values,
                        Scalar::List {
                            element: element.erase(),
                            items: Vec::new(),
                        },
                        control,
                        visitor,
                    )?;
                    values
                }
                Type::Option(element) => {
                    let mut values = Vec::new();
                    emit(
                        &mut values,
                        Scalar::Option {
                            element: (**element).erase(),
                            value: None,
                        },
                        control,
                        visitor,
                    )?;
                    let Some(items) = enumerate(
                        element,
                        law,
                        control,
                        roster,
                        owned,
                        dependencies,
                        &mut |_| {},
                        partial_maps,
                        active,
                        allow_degenerate,
                    )?
                    else {
                        return Ok(None);
                    };
                    for item in items {
                        tick(control)?;
                        emit(
                            &mut values,
                            Scalar::Option {
                                element: (**element).erase(),
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
                    let Some(items) = enumerate(
                        element,
                        law,
                        control,
                        roster,
                        owned,
                        dependencies,
                        &mut |_| {},
                        partial_maps,
                        active,
                        allow_degenerate,
                    )?
                    else {
                        return Ok(None);
                    };
                    for item in items {
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
                            data::set((**element).erase(), &subset, control)?,
                            control,
                            visitor,
                        )?;
                    }
                    values
                }
                Type::Data(family) => {
                    if allow_degenerate && active.contains(family) {
                        return Ok(None);
                    }
                    if allow_degenerate {
                        active.push(family.clone());
                    }
                    let result = (|| -> Result<Option<Vec<Scalar>>, ValidationFailure> {
                        let mut values = Vec::new();
                        for ctor in data::constructors(law, family)? {
                            tick(control)?;
                            let Some(rows) = product(
                                &ctor.arguments,
                                law,
                                control,
                                roster,
                                owned,
                                dependencies,
                                partial_maps,
                                active,
                                allow_degenerate,
                            )?
                            else {
                                return Ok(None);
                            };
                            for args in rows {
                                tick(control)?;
                                emit(
                                    &mut values,
                                    Scalar::Data {
                                        family: family.clone(),
                                        constructor: law
                                            .resolved_names()
                                            .get(&format!("{family}.{}", ctor.name))
                                            .ok_or("constructorの検査済み名がない")?
                                            .clone(),
                                        args,
                                    },
                                    control,
                                    visitor,
                                )?;
                                tick(control)?;
                            }
                        }
                        Ok(Some(values))
                    })();
                    if allow_degenerate {
                        active.pop();
                    }
                    let Some(values) = result? else {
                        return Ok(None);
                    };
                    values
                }
                _ if allow_degenerate => return Ok(None),
                _ => return Err("有限全域でない型を列挙した".into()),
            };
            tick(control)?;
            Ok(Some(values))
        })
    }
    let mut enumeration = FiniteDomain::default();
    let Some(values) = enumerate(
        ty,
        law,
        control,
        roster,
        owned,
        &mut enumeration,
        visitor,
        partial_maps,
        &mut Vec::new(),
        allow_degenerate,
    )?
    else {
        return Ok(None);
    };
    enumeration.enumeration.values = values;
    enumeration.enumeration.support.sort();
    enumeration.enumeration.support.dedup();
    enumeration.missing.sort();
    enumeration.missing.dedup();
    Ok(Some(enumeration))
}
