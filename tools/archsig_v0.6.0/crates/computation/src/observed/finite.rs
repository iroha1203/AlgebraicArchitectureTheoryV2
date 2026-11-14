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
        &mut |_, _| Err(internal!("有限全域でない型を列挙した").into()),
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
        &mut |_, _| Err(internal!("field候補に消去前のOwned型がある").into()),
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
    .ok_or_else(|| internal!("有限全域でない型を列挙した").into())
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
                    // Enumeration is also called internally without supported(); reject
                    // hand-built non-reference Maps before enumerating either endpoint.
                    let domain_entity = domain
                        .ref_target()
                        .ok_or(internal!("Mapの始域型が参照でない"))?;
                    let codomain_entity = codomain
                        .ref_target()
                        .ok_or(internal!("Mapの終域型が参照でない"))?;
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
                                domain: domain_entity.to_owned(),
                                codomain: codomain_entity.to_owned(),
                                pairs: pairs.into(),
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
                        .map_err(|_| internal!("有限型Fpの素数が不正"))?;
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
                    // The former doubling construction emitted subsets in binary
                    // order, with the first roster entry as the least significant
                    // bit. Keep that order (including duplicate candidates), but
                    // construct only the subset being emitted. A bit vector avoids
                    // imposing a machine-word bound on the finite element domain.
                    let mut selected = vec![false; items.len()];
                    let mut values = Vec::new();
                    'subsets: loop {
                        tick(control)?;
                        let mut subset = Vec::new();
                        for (item, selected) in items.iter().zip(&selected) {
                            tick(control)?;
                            if *selected {
                                subset.push(item.clone());
                            }
                        }
                        emit(
                            &mut values,
                            data::set((**element).erase(), &subset, control)?,
                            control,
                            visitor,
                        )?;
                        let mut index = 0;
                        loop {
                            tick(control)?;
                            if index == selected.len() {
                                break 'subsets;
                            }
                            selected[index] = !selected[index];
                            if selected[index] {
                                break;
                            }
                            index += 1;
                        }
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
                                        constructor: crate::observed::result::DataConstructor::new(
                                            family,
                                            law.resolved_names()
                                                .get(&format!("{family}.{}", ctor.name))
                                                .ok_or(internal!("constructorの検査済み名がない"))?
                                                .clone(),
                                        )?,
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
                _ => return Err(internal!("有限全域でない型を列挙した").into()),
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

#[cfg(test)]
mod map_endpoint_tests {
    use super::*;
    #[allow(dead_code)]
    mod fixture {
        include!("../../../../tests/common/finite_map.rs");
    }
    fn law() -> CheckedLaw {
        let definitions = archsig_input::definition::check_definitions(&[(
            "maps",
            fixture::DEFINITIONS.as_bytes(),
        )])
        .unwrap();
        archsig_input::law::check_law(
            fixture::law(&definitions.vocabularies()["Maps"].digest).as_bytes(),
            &definitions,
        )
        .unwrap()
    }
    #[test]
    fn internal_nonreference_map_endpoints_are_errors_before_enumeration() {
        let law = law();
        for (from, to, message) in [
            (Type::Fp("2".into()), Type::Unit, "Mapの始域型が参照でない"),
            (
                Type::Ref("Maps.Key".into()),
                Type::Unit,
                "Mapの終域型が参照でない",
            ),
        ] {
            let ty = Type::Map(Box::new(from), Box::new(to));
            let result = values(
                &ty,
                &law,
                &Control::unlimited(),
                &mut |_| panic!("invalid endpoints must be rejected before roster access"),
                &mut |_| panic!("invalid endpoints must not publish a value"),
            );
            assert!(matches!(result, Err(ValidationFailure::Internal(ref error))
                if error.message() == message));
            let result = field_candidates_if_finite(&ty, &law, &Control::unlimited(), &mut |_| {
                panic!("invalid if-finite endpoints must not read a roster")
            });
            assert!(matches!(result, Err(ValidationFailure::Internal(ref error))
                if error.message() == message));
        }
    }
    #[test]
    fn public_law_rejects_nonreference_map_endpoint_types() {
        let definitions = archsig_input::definition::check_definitions(&[(
            "maps",
            fixture::DEFINITIONS.as_bytes(),
        )])
        .unwrap();
        let digest = &definitions.vocabularies()["Maps"].digest;
        for ty in ["Map<Fp(2),Unit>", "Map<Key,Unit>"] {
            let source = fixture::law(digest).replace("Map<Key,Image>", ty);
            let failure =
                archsig_input::law::check_law(source.as_bytes(), &definitions).unwrap_err();
            assert_eq!(failure.issue.code, archsig_common::issue::Code::Syntax);
            assert_eq!(
                failure.issue.message,
                "Map domain and codomain must be reference types"
            );
        }
    }
    #[test]
    fn empty_owned_map_keeps_erased_endpoint_types_and_owner_roster() {
        let law = law();
        let ty = Type::Map(
            Box::new(Type::Owned("Maps.Key".into(), "from".into())),
            Box::new(Type::Owned("Maps.Image".into(), "to".into())),
        );
        let mut owners = Vec::new();
        let result = values_with_owned(
            &ty,
            &law,
            &Control::unlimited(),
            &mut |_| panic!("Owned domains must use their owner roster"),
            &mut |entity, owner| {
                owners.push((entity.to_owned(), owner.to_owned()));
                Ok(Enumeration::default())
            },
            &mut |_| {},
        )
        .unwrap();
        assert_eq!(
            owners,
            [
                ("Maps.Key".into(), "from".into()),
                ("Maps.Image".into(), "to".into())
            ]
        );
        assert_eq!(result.values.len(), 1);
        let value = &result.values[0];
        assert_eq!(value.ty(), ty.erase());
        assert_eq!(value.wire(), archsig_common::canonical::Json::Arr(vec![]));
        assert_eq!(value.clone(), *value);
    }
}

#[cfg(test)]
mod set_enumeration_tests {
    use super::*;
    use archsig_common::control::Signal;
    use std::{cell::Cell, rc::Rc};

    fn law() -> CheckedLaw {
        let definitions = archsig_input::definition::check_definitions(&[(
            "sets",
            br#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Sets","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Sets.Item","meaning":"Item","parameters":[],"fields":[],"alignments":[]}]}]}"#.as_slice(),
        )])
        .unwrap();
        archsig_input::law::check_law(
            format!(
                "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Sets {{ use vocabulary Sets version \"1\" digest \"{}\"; view seed():Bool=true; }}",
                definitions.vocabularies()["Sets"].digest,
            )
            .as_bytes(),
            &definitions,
        )
        .unwrap()
    }

    fn item(index: usize) -> Scalar {
        Scalar::Subject {
            snapshot: "v".into(),
            subject: format!("item{index}"),
            entity: "Sets.Item".into(),
        }
    }

    fn enumerate_set(
        items: &[Scalar],
        control: &Control,
        visitor: &mut dyn FnMut(usize),
    ) -> Result<Enumeration, ValidationFailure> {
        values(
            &Type::Set(Box::new(Type::Ref("Sets.Item".into()))),
            &law(),
            control,
            &mut |entity| {
                assert_eq!(entity, "Sets.Item");
                Ok(Enumeration {
                    values: items.to_vec(),
                    ..Enumeration::default()
                })
            },
            visitor,
        )
    }

    // Independent, small reference for the previous doubling algorithm. Set
    // normalization is deliberately unchanged; roster and result duplicates stay.
    fn doubling_reference(items: &[Scalar]) -> Vec<Scalar> {
        let mut subsets = vec![Vec::new()];
        for item in items {
            let count = subsets.len();
            for index in 0..count {
                let mut subset = subsets[index].clone();
                subset.push(item.clone());
                subsets.push(subset);
            }
        }
        subsets
            .iter()
            .map(|subset| {
                data::set(Type::Ref("Sets.Item".into()), subset, &Control::unlimited()).unwrap()
            })
            .collect()
    }

    #[test]
    fn set_values_preserve_doubling_order_empty_domain_and_duplicates() {
        let mut domains = (0..=5)
            .map(|size| (0..size).map(item).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        domains.push(vec![item(2), item(0), item(2), item(1)]);
        for items in domains {
            let mut visited = Vec::new();
            let actual = enumerate_set(&items, &Control::unlimited(), &mut |index| {
                visited.push(index);
            })
            .unwrap();
            assert_eq!(actual.values, doubling_reference(&items));
            assert_eq!(visited, (0..actual.values.len()).collect::<Vec<_>>());
            assert_eq!(actual.values.len(), 1 << items.len());
        }
    }

    #[test]
    fn nested_sets_and_option_elements_keep_their_complete_domains() {
        let law = law();
        for (element, count) in [
            (Type::Set(Box::new(Type::Bool)), 16),
            (Type::Option(Box::new(Type::Unit)), 4),
        ] {
            let actual = values(
                &Type::Set(Box::new(element)),
                &law,
                &Control::unlimited(),
                &mut |_| panic!("value-only domains do not read a roster"),
                &mut |_| {},
            )
            .unwrap();
            assert_eq!(actual.values.len(), count);
            assert!(matches!(&actual.values[0], Scalar::Set { items, .. } if items.is_empty()));
        }
    }

    #[test]
    fn first_set_value_is_visited_without_constructing_the_powerset() {
        // More elements than a machine-word bit mask can cover. The budget is
        // deterministic: the old precomputation exhausts it before any visit.
        let checkpoints = Rc::new(Cell::new(0));
        let mut visited = Vec::new();
        let cancelled = Rc::new(Cell::new(false));
        let stop = cancelled.clone();
        let count = checkpoints.clone();
        let control = Control::new(move |_| {
            count.set(count.get() + 1);
            (stop.get() || count.get() >= 1000).then_some(Signal::Term)
        });
        let result = enumerate_set(
            &(0..80).map(item).collect::<Vec<_>>(),
            &control,
            &mut |index| {
                visited.push(index);
                cancelled.set(true);
            },
        );
        assert!(matches!(result, Err(ValidationFailure::Stop(Signal::Term))));
        assert_eq!(visited, [0]);
        assert!(checkpoints.get() < 1000);
    }

    #[test]
    fn visitor_cancellation_stops_without_visiting_another_subset() {
        for stop_index in [0, 3, 7] {
            let flag = std::sync::Arc::new(std::sync::atomic::AtomicI32::new(0));
            let control = Control::from_signal_flag(flag.clone(), 1, 2);
            let mut visited = Vec::new();
            let result = enumerate_set(
                &(0..4).map(item).collect::<Vec<_>>(),
                &control,
                &mut |index| {
                    visited.push(index);
                    if index == stop_index {
                        flag.store(1, std::sync::atomic::Ordering::Relaxed);
                    }
                },
            );
            assert!(matches!(result, Err(ValidationFailure::Stop(Signal::Int))));
            assert_eq!(visited, (0..=stop_index).collect::<Vec<_>>());
        }
    }

    #[test]
    fn finite_checkpoint_cancellation_propagates_at_every_iteration_boundary() {
        let checkpoints = Rc::new(Cell::new(0));
        let count = checkpoints.clone();
        let control = Control::new(move |point| {
            assert_eq!(point, Checkpoint::FiniteIteration);
            count.set(count.get() + 1);
            None
        });
        enumerate_set(&[item(0), item(1)], &control, &mut |_| {}).unwrap();
        for cutoff in 1..=checkpoints.get() {
            let calls = Rc::new(Cell::new(0));
            let count = calls.clone();
            let control = Control::new(move |_| {
                count.set(count.get() + 1);
                (count.get() == cutoff).then_some(Signal::Term)
            });
            let result = enumerate_set(&[item(0), item(1)], &control, &mut |_| {});
            assert!(
                matches!(result, Err(ValidationFailure::Stop(Signal::Term))),
                "cutoff {cutoff}"
            );
            assert_eq!(calls.get(), cutoff);
        }
    }
}
