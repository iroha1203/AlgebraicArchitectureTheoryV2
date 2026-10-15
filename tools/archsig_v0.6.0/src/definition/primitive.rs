//! 共通原始定義の型適格性・所属・対応・有限 data の検査。
//! 原始署名・Type・実入力位置から直接検査し、解決した構造を同じ表へ保持する。
use super::*;
use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};
use crate::{prime::is_prime, types::Type};
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};
type R<T, E = Box<Issue>> = Result<T, E>;

pub(crate) fn child(parent: &Location, token: &str) -> Location {
    match parent {
        Location::Definition { input, pointer, .. } => {
            location(input, &crate::json::pointer_push(pointer, token))
        }
        Location::ArchMap { pointer, .. } => Location::ArchMap {
            pointer: crate::json::pointer_push(pointer, token),
            span: None,
        },
        Location::Law { .. } => parent.clone(),
    }
}
fn fail<T, E: InputError>(code: Code, at: &Location, message: impl Into<String>) -> R<T, E> {
    Err(Box::new(Issue {
        code,
        message: message.into(),
        location: at.clone(),
        details: Details::Empty,
    })
    .into())
}
fn mismatch<T, E: InputError>(
    at: &Location,
    expected: &Type,
    actual: &Type,
    message: impl Into<String>,
    control: &mut Control,
) -> R<T, E> {
    let message = message.into();
    let details: R<Details, E> = (|| {
        Ok(Details::Type {
            expected: expected.erase_controlled::<E>(control, Checkpoint::DefinitionSemantics)?,
            actual: actual.erase_controlled::<E>(control, Checkpoint::DefinitionSemantics)?,
        })
    })();
    let details = match details {
        Ok(details) => details,
        // Complete only the payload of the already detected mismatch.
        Err(stop) if stop.is_budget_stop() => Details::Type {
            expected: expected.erase(),
            actual: actual.erase(),
        },
        Err(stop) => return Err(stop),
    };
    Err(Box::new(Issue {
        code: Code::Type,
        message,
        location: at.clone(),
        details,
    })
    .into())
}

impl CheckedDefinitions {
    /// data を通じた参照・Term の包含を、原始定義だけから固定点で計算する。
    pub fn data_properties(&self) -> BTreeMap<String, DataProperties> {
        self.data_properties_controlled::<Box<Issue>>(&mut Control::unlimited())
            .expect("通常の性質計算は中断しない")
    }
    /// 同じ固定点計算に検査の共有制御を渡す。
    pub(crate) fn data_properties_controlled<E: InputError>(
        &self,
        control: &mut Control,
    ) -> R<BTreeMap<String, DataProperties>, E> {
        let mut props = BTreeMap::new();
        for (name, d) in &self.declarations {
            E::checkpoint(control, Checkpoint::DefinitionData)?;
            if matches!(d.signature, PrimitiveSignature::Data { .. }) {
                props.insert(name.clone(), DataProperties::default());
            }
            E::checkpoint(control, Checkpoint::DefinitionData)?;
        }
        loop {
            E::checkpoint(control, Checkpoint::DefinitionData)?;
            let mut changed = false;
            for (name, d) in &self.declarations {
                E::checkpoint(control, Checkpoint::DefinitionData)?;
                let PrimitiveSignature::Data { constructors } = &d.signature else {
                    continue;
                };
                let mut p = DataProperties::default();
                for constructor in constructors {
                    E::checkpoint(control, Checkpoint::DefinitionData)?;
                    for t in &constructor.arguments {
                        E::checkpoint(control, Checkpoint::DefinitionData)?;
                        p.term_or_path |= has_term_or_path::<E>(t, &props, control)?;
                        p.reference |= has_reference::<E>(t, &props, control)?;
                        E::checkpoint(control, Checkpoint::DefinitionData)?;
                    }
                    E::checkpoint(control, Checkpoint::DefinitionData)?;
                }
                if props[name] != p {
                    props.insert(name.clone(), p);
                    changed = true;
                }
                E::checkpoint(control, Checkpoint::DefinitionData)?;
            }
            E::checkpoint(control, Checkpoint::DefinitionData)?;
            if !changed {
                return Ok(props);
            }
            E::checkpoint(control, Checkpoint::DefinitionData)?;
        }
    }
    /// 完全名へ解決済みの原始型を、左にある parameter と実入力位置で検査する。
    pub fn check_primitive_type(
        &self,
        ty: &Type,
        at: &Location,
        earlier: &[(&str, &Type)],
    ) -> R<()> {
        let mut control = Control::unlimited();
        let props = self.data_properties_controlled::<Box<Issue>>(&mut control)?;
        check_type::<Box<Issue>>(self, &props, ty, at, earlier, &mut control)
    }
    pub fn is_root_entity(&self, name: &str) -> bool {
        self.is_root_entity_controlled::<Box<Issue>>(name, &mut Control::unlimited())
            .expect("通常の所属検査は中断しない")
    }
    pub(crate) fn is_root_entity_controlled<E: InputError>(
        &self,
        name: &str,
        control: &mut Control,
    ) -> R<bool, E> {
        E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
        let result = (|| match self.declarations.get(name) {
            Some(d) if matches!(d.signature, PrimitiveSignature::Entity { .. }) => Ok(d
                .signature
                .field_controlled::<E>("owner", control, Checkpoint::DefinitionSemantics)?
                .is_none()),
            _ => Ok(false),
        })();
        E::finish(result, control, Checkpoint::DefinitionSemantics)
    }
    /// 原始署名に明記した所属先。検査中にも宣言順に依存せず読める。
    pub fn owner_root(&self, name: &str) -> Option<&str> {
        self.owner_root_controlled::<Box<Issue>>(name, &mut Control::unlimited())
            .expect("通常の所属検査は中断しない")
    }
    pub(crate) fn owner_root_controlled<E: InputError>(
        &self,
        name: &str,
        control: &mut Control,
    ) -> R<Option<&str>, E> {
        E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
        let result = (|| {
            let Some(d) = self.declarations.get(name) else {
                return Ok(None);
            };
            if !matches!(
                d.signature,
                PrimitiveSignature::Entity { .. } | PrimitiveSignature::Arrow { .. }
            ) {
                return Ok(None);
            }
            let Some(field) = d.signature.field_controlled::<E>(
                "owner",
                control,
                Checkpoint::DefinitionSemantics,
            )?
            else {
                return Ok(None);
            };
            let Type::Ref(root) = &field.ty else {
                return Ok(None);
            };
            Ok(self
                .is_root_entity_controlled::<E>(root, control)?
                .then_some(root.as_str()))
        })();
        E::finish(result, control, Checkpoint::DefinitionSemantics)
    }
}
/// 型の各成分の前後で確認し、短絡しても中断を bool に変換しない。
fn type_any<E: InputError>(
    t: &Type,
    predicate: &mut impl FnMut(&Type) -> bool,
    control: &mut Control,
) -> R<bool, E> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        E::checkpoint(control, Checkpoint::DefinitionData)?;
        let found = if predicate(t) {
            true
        } else {
            match t {
                Type::Tuple(items) => {
                    let mut found = false;
                    for item in items {
                        E::checkpoint(control, Checkpoint::DefinitionData)?;
                        if type_any::<E>(item, predicate, control)? {
                            found = true;
                            break;
                        }
                        E::checkpoint(control, Checkpoint::DefinitionData)?;
                    }
                    found
                }
                Type::List(t) | Type::Set(t) | Type::Option(t) => {
                    type_any::<E>(t, predicate, control)?
                }
                Type::Map(a, b) => {
                    type_any::<E>(a, predicate, control)? || type_any::<E>(b, predicate, control)?
                }
                Type::Term(args, ret) => {
                    let mut found = false;
                    for arg in args {
                        E::checkpoint(control, Checkpoint::DefinitionData)?;
                        if type_any::<E>(arg, predicate, control)? {
                            found = true;
                            break;
                        }
                        E::checkpoint(control, Checkpoint::DefinitionData)?;
                    }
                    found || type_any::<E>(ret, predicate, control)?
                }
                _ => false,
            }
        };
        E::checkpoint(control, Checkpoint::DefinitionData)?;
        Ok(found)
    })
}
fn has_term_or_path<E: InputError>(
    t: &Type,
    props: &BTreeMap<String, DataProperties>,
    control: &mut Control,
) -> R<bool, E> {
    type_any::<E>(
        t,
        &mut |t| match t {
            Type::Term(..) | Type::Path(..) => true,
            Type::Data(n) => props.get(n).is_some_and(|p| p.term_or_path),
            _ => false,
        },
        control,
    )
}
fn has_reference<E: InputError>(
    t: &Type,
    props: &BTreeMap<String, DataProperties>,
    control: &mut Control,
) -> R<bool, E> {
    type_any::<E>(
        t,
        &mut |t| match t {
            Type::Ref(_) | Type::Owned(..) | Type::Map(..) | Type::Path(..) => true,
            Type::Data(n) => props.get(n).is_some_and(|p| p.reference),
            _ => false,
        },
        control,
    )
}
fn check_type<E: InputError>(
    defs: &CheckedDefinitions,
    props: &BTreeMap<String, DataProperties>,
    t: &Type,
    at: &Location,
    earlier: &[(&str, &Type)],
    control: &mut Control,
) -> R<(), E> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
        let result = check_type_inner::<E>(defs, props, t, at, earlier, control);
        E::finish(result, control, Checkpoint::DefinitionSemantics)
    })
}
fn check_type_inner<E: InputError>(
    defs: &CheckedDefinitions,
    props: &BTreeMap<String, DataProperties>,
    t: &Type,
    at: &Location,
    earlier: &[(&str, &Type)],
    control: &mut Control,
) -> R<(), E> {
    E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
    match t {
        Type::Unit | Type::Bool | Type::Z | Type::Q | Type::Text => {}
        Type::Fp(modulus) => {
            let Ok(n) = modulus.parse::<BigUint>() else {
                return fail(Code::Syntax, at, "Fp の法は正の10進整数文字列");
            };
            if !is_prime(&n) {
                return fail(Code::Syntax, at, format!("Fp の法 {modulus} は素数でない"));
            }
        }
        Type::Ref(name) | Type::Data(name) | Type::Owned(name, _) => {
            let Some(d) = defs.declarations.get(name) else {
                return fail(
                    Code::Reference,
                    &child(at, "1"),
                    format!("型名 `{name}` を解決できない"),
                );
            };
            if matches!(t, Type::Data(_)) != matches!(d.signature, PrimitiveSignature::Data { .. })
            {
                return fail(
                    Code::Syntax,
                    &child(at, "1"),
                    "Ref/Data の型タグと参照先の宣言種別が異なる",
                );
            }
            if let Type::Owned(_, index) = t {
                let Some(root) = defs.owner_root_controlled::<E>(name, control)? else {
                    return fail(
                        Code::Syntax,
                        at,
                        format!("`{name}` は所属先を持たない entity・arrow"),
                    );
                };
                let mut parameter = None;
                for (name, ty) in earlier {
                    E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
                    let found = *name == index;
                    E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
                    if found {
                        parameter = Some(*ty);
                        break;
                    }
                }
                let Some(param) = parameter else {
                    return fail(
                        Code::Reference,
                        &child(at, "2"),
                        format!("添字 `{index}` は左にある parameter を指す"),
                    );
                };
                let expected = Type::Ref(root.into());
                if param.erase_controlled::<E>(control, Checkpoint::DefinitionSemantics)?
                    != expected
                {
                    return mismatch(
                        &child(at, "2"),
                        &expected,
                        param,
                        "添字の parameter は所属先の根 entity の参照",
                        control,
                    );
                }
            }
        }
        Type::Tuple(items) => {
            for (i, t) in items.iter().enumerate() {
                E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
                check_type::<E>(
                    defs,
                    props,
                    t,
                    &child(at, &(i + 1).to_string()),
                    earlier,
                    control,
                )?;
                E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
            }
        }
        Type::List(t) | Type::Option(t) => {
            check_type::<E>(defs, props, t, &child(at, "1"), earlier, control)?
        }
        Type::Set(t) => {
            check_type::<E>(defs, props, t, &child(at, "1"), earlier, control)?;
            if has_term_or_path::<E>(t, props, control)? {
                return fail(Code::Syntax, at, "Set の要素型は Term・Path を含まない");
            }
        }
        Type::Map(a, b) => {
            check_type::<E>(defs, props, a, &child(at, "1"), earlier, control)?;
            check_type::<E>(defs, props, b, &child(at, "2"), earlier, control)?;
            if a.ref_target().is_none() || b.ref_target().is_none() {
                return fail(Code::Syntax, at, "Map の定義域・値域は参照型");
            }
        }
        Type::Term(args, ret) => {
            let args_at = child(at, "1");
            for (i, t) in args.iter().enumerate() {
                E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
                check_type::<E>(
                    defs,
                    props,
                    t,
                    &child(&args_at, &i.to_string()),
                    &[],
                    control,
                )?;
                E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
            }
            check_type::<E>(defs, props, ret, &child(at, "2"), &[], control)?;
            let mut references = false;
            for arg in args {
                E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
                references |= has_reference::<E>(arg, props, control)?;
                E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
            }
            if references || has_reference::<E>(ret, props, control)? {
                return fail(
                    Code::Syntax,
                    at,
                    "Term の引数・戻り型は参照・Map・Path を含まない値型",
                );
            }
        }
        Type::Path(..) => {
            return fail(
                Code::Syntax,
                at,
                "Path は原始 field・data・Term の型に置けない",
            );
        }
    }
    E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
    Ok(())
}

pub(super) fn check<E: InputError>(
    defs: &mut CheckedDefinitions,
    control: &mut Control,
) -> R<(), E> {
    let props = defs.data_properties_controlled::<E>(control)?;
    for d in defs.declarations.values() {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        if let Some((parameters, fields)) = d.signature.record_fields() {
            let mut earlier = Vec::new();
            for p in parameters {
                E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                check_type::<E>(
                    defs,
                    &props,
                    &p.ty,
                    &child(&p.location, "type"),
                    &earlier,
                    control,
                )?;
                earlier.push((p.name.as_str(), &p.ty));
                E::checkpoint(control, Checkpoint::DefinitionDependency)?;
            }
            for f in fields {
                E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                check_type::<E>(
                    defs,
                    &props,
                    &f.ty,
                    &child(&f.location, "type"),
                    &earlier,
                    control,
                )?;
                E::checkpoint(control, Checkpoint::DefinitionDependency)?;
            }
        } else if let PrimitiveSignature::Data { constructors } = &d.signature {
            for c in constructors {
                E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                let args_at = child(&c.location, "arguments");
                for (i, t) in c.arguments.iter().enumerate() {
                    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                    check_type::<E>(
                        defs,
                        &props,
                        t,
                        &child(&args_at, &i.to_string()),
                        &[],
                        control,
                    )?;
                    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                }
                E::checkpoint(control, Checkpoint::DefinitionDependency)?;
            }
        }
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    // 解決した owner/endpoint は同じ原始表に保持し、reading ごとの複製を作らない。
    let names: Vec<_> = defs.declarations.keys().cloned().collect();
    for name in &names {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        let d = &defs.declarations[name];
        let resolved = match &d.signature {
            PrimitiveSignature::Entity { .. } => {
                let owner = if let Some(f) = d.signature.field_controlled::<E>(
                    "owner",
                    control,
                    Checkpoint::DefinitionSemantics,
                )? {
                    match &f.ty {
                        Type::Ref(r) if defs.is_root_entity_controlled::<E>(r, control)? => {
                            Some(r.clone())
                        }
                        _ => {
                            return fail(
                                Code::Syntax,
                                &child(&f.location, "name"),
                                "owner の型は所属先を持たない entity",
                            );
                        }
                    }
                } else {
                    None
                };
                Some((owner, None))
            }
            PrimitiveSignature::Arrow { .. } => {
                let (Some(owner), Some(from), Some(to)) = (
                    d.signature.field_controlled::<E>(
                        "owner",
                        control,
                        Checkpoint::DefinitionSemantics,
                    )?,
                    d.signature.field_controlled::<E>(
                        "from",
                        control,
                        Checkpoint::DefinitionSemantics,
                    )?,
                    d.signature.field_controlled::<E>(
                        "to",
                        control,
                        Checkpoint::DefinitionSemantics,
                    )?,
                ) else {
                    return fail(
                        Code::Syntax,
                        &child(&d.location, "name"),
                        "arrow は owner・from・to の field を持つ",
                    );
                };
                let root = match &owner.ty {
                    Type::Ref(r) if defs.is_root_entity_controlled::<E>(r, control)? => r.clone(),
                    _ => {
                        return fail(
                            Code::Syntax,
                            &child(&owner.location, "name"),
                            "arrow の owner の型は根 entity",
                        );
                    }
                };
                let endpoint = match (&from.ty, &to.ty) {
                    (Type::Owned(e, p), Type::Owned(f, q))
                        if e == f && p == "owner" && q == "owner" =>
                    {
                        e.clone()
                    }
                    _ => {
                        return fail(
                            Code::Syntax,
                            &child(&from.location, "name"),
                            "arrow の from・to は同じ entity の E[owner]",
                        );
                    }
                };
                if !defs
                    .declarations
                    .get(&endpoint)
                    .is_some_and(|d| matches!(d.signature, PrimitiveSignature::Entity { .. }))
                    || defs.owner_root_controlled::<E>(&endpoint, control)? != Some(root.as_str())
                {
                    return fail(
                        Code::Syntax,
                        &child(&from.location, "name"),
                        "arrow の端点は owner に所属する entity",
                    );
                }
                Some((Some(root), Some(endpoint)))
            }
            _ => None,
        };
        if let Some((owner, endpoint)) = resolved {
            let d = defs.declarations.get_mut(name).expect("登録済み");
            match &mut d.signature {
                PrimitiveSignature::Entity { owner: o, .. } => *o = owner,
                PrimitiveSignature::Arrow {
                    owner: o,
                    endpoint: e,
                    ..
                } => {
                    *o = owner.expect("arrow owner");
                    *e = endpoint.expect("arrow endpoint")
                }
                _ => unreachable!(),
            }
        }
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    check_data::<E>(defs, control)?;
    for name in names {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        if matches!(
            defs.declarations[&name].signature,
            PrimitiveSignature::Correspondence { .. }
        ) {
            check_correspondence::<E>(defs, &props, &name, control)?
        }
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    Ok(())
}

fn check_data<E: InputError>(defs: &CheckedDefinitions, control: &mut Control) -> R<(), E> {
    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (name, d) in &defs.declarations {
        E::checkpoint(control, Checkpoint::DefinitionData)?;
        let PrimitiveSignature::Data { constructors } = &d.signature else {
            continue;
        };
        for c in constructors {
            E::checkpoint(control, Checkpoint::DefinitionData)?;
            for (i, t) in c.arguments.iter().enumerate() {
                E::checkpoint(control, Checkpoint::DefinitionData)?;
                if !positive_self::<E>(t, name, true, control)? {
                    return fail(
                        Code::Syntax,
                        &child(&child(&c.location, "arguments"), &i.to_string()),
                        "data の自己参照は直接または Tuple・List・Option を通る",
                    );
                }
                type_any::<E>(
                    t,
                    &mut |t| {
                        if let Type::Data(other) = t {
                            if other != name {
                                edges.entry(name.clone()).or_default().insert(other.clone());
                            }
                        }
                        false
                    },
                    control,
                )?;
                E::checkpoint(control, Checkpoint::DefinitionData)?;
            }
            E::checkpoint(control, Checkpoint::DefinitionData)?;
        }
        E::checkpoint(control, Checkpoint::DefinitionData)?;
    }
    if let Some(n) = find_cycle_controlled::<E>(&edges, control)? {
        return fail(
            Code::Cycle,
            &child(&defs.declarations[&n].location, "name"),
            format!("data `{n}` が相互再帰している"),
        );
    }
    let mut inhabited = BTreeSet::new();
    loop {
        E::checkpoint(control, Checkpoint::DefinitionData)?;
        let mut changed = false;
        for (name, d) in &defs.declarations {
            E::checkpoint(control, Checkpoint::DefinitionData)?;
            if inhabited.contains(name) {
                continue;
            }
            let PrimitiveSignature::Data { constructors } = &d.signature else {
                continue;
            };
            let mut has_constructor = false;
            for constructor in constructors {
                E::checkpoint(control, Checkpoint::DefinitionData)?;
                let mut all_inhabited = true;
                for t in &constructor.arguments {
                    E::checkpoint(control, Checkpoint::DefinitionData)?;
                    if !type_inhabited::<E>(t, &inhabited, control)? {
                        all_inhabited = false;
                        break;
                    }
                    E::checkpoint(control, Checkpoint::DefinitionData)?;
                }
                if all_inhabited {
                    has_constructor = true;
                    break;
                }
                E::checkpoint(control, Checkpoint::DefinitionData)?;
            }
            if has_constructor {
                inhabited.insert(name.clone());
                changed = true;
            }
            E::checkpoint(control, Checkpoint::DefinitionData)?;
        }
        if !changed {
            break;
        }
        E::checkpoint(control, Checkpoint::DefinitionData)?;
    }
    for (name, d) in &defs.declarations {
        E::checkpoint(control, Checkpoint::DefinitionData)?;
        if matches!(d.signature, PrimitiveSignature::Data { .. }) && !inhabited.contains(name) {
            return fail(
                Code::Syntax,
                &child(&d.location, "name"),
                format!("data `{name}` は有限の値を持たない"),
            );
        }
        E::checkpoint(control, Checkpoint::DefinitionData)?;
    }
    E::checkpoint(control, Checkpoint::DefinitionData)?;
    Ok(())
}
fn owned_types<E: InputError>(
    defs: &CheckedDefinitions,
    root: &str,
    control: &mut Control,
) -> R<BTreeSet<String>, E> {
    let mut owned = BTreeSet::new();
    for name in defs.declarations.keys() {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        if defs.owner_root_controlled::<E>(name, control)? == Some(root) {
            owned.insert(name.clone());
        }
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    Ok(owned)
}
fn check_correspondence<E: InputError>(
    defs: &mut CheckedDefinitions,
    props: &BTreeMap<String, DataProperties>,
    name: &str,
    control: &mut Control,
) -> R<(), E> {
    let d = &defs.declarations[name];
    let PrimitiveSignature::Correspondence {
        parameters,
        fields,
        alignments,
        ..
    } = &d.signature
    else {
        unreachable!()
    };
    let (Some(from), Some(to)) = (
        super::model::find_field_controlled::<E>(
            parameters,
            "from",
            control,
            Checkpoint::DefinitionSemantics,
        )?,
        super::model::find_field_controlled::<E>(
            parameters,
            "to",
            control,
            Checkpoint::DefinitionSemantics,
        )?,
    ) else {
        return fail(
            Code::Syntax,
            &child(&d.location, "name"),
            "correspondence は parameters に from・to を持つ",
        );
    };
    let mut root = |p: &Field| -> R<String, E> {
        match &p.ty {
            Type::Ref(n) if defs.is_root_entity_controlled::<E>(n, control)? => Ok(n.clone()),
            _ => fail(
                Code::Syntax,
                &child(&p.location, "name"),
                "correspondence の from・to は根 entity",
            ),
        }
    };
    let source = root(from)?;
    let target = root(to)?;
    let mut maps = Vec::new();
    let mut domain = BTreeMap::new();
    let mut codomain = BTreeSet::new();
    for m in fields {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        let (e, f) = match &m.ty {
            Type::Map(a, b) => match (a.as_ref(), b.as_ref()) {
                (Type::Owned(e, p), Type::Owned(f, q)) if p == "from" && q == "to" => {
                    (e.clone(), f.clone())
                }
                _ => {
                    return fail(
                        Code::Syntax,
                        &child(&m.location, "name"),
                        "correspondence の field は Map<E[from], F[to]>",
                    );
                }
            },
            _ => {
                return fail(
                    Code::Syntax,
                    &child(&m.location, "name"),
                    "correspondence の field は Map<E[from], F[to]>",
                );
            }
        };
        if defs.owner_root_controlled::<E>(&e, control)? != Some(source.as_str())
            || defs.owner_root_controlled::<E>(&f, control)? != Some(target.as_str())
        {
            return fail(
                Code::Syntax,
                &child(&m.location, "name"),
                "対応表の型は from・to の根に所属する",
            );
        }
        if domain.insert(e.clone(), f.clone()).is_some() || !codomain.insert(f.clone()) {
            return fail(
                Code::DuplicateId,
                &child(&m.location, "name"),
                "同じ型の対応表が重複している",
            );
        }
        maps.push((m.name.clone(), e, f));
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    if domain.keys().cloned().collect::<BTreeSet<_>>() != owned_types::<E>(defs, &source, control)?
        || codomain != owned_types::<E>(defs, &target, control)?
    {
        return fail(
            Code::Syntax,
            &child(&d.location, "name"),
            "correspondence は from・to の根に所属する全ての entity・arrow を一度ずつ覆う",
        );
    }
    let mut mu = domain.clone();
    mu.insert(source.clone(), target.clone());
    let mut explicit = BTreeMap::new();
    let mut targets = BTreeSet::new();
    for a in alignments {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        let (se, _) = resolve_field::<E>(defs, &a.source, &child(&a.location, "source"), control)?;
        let (te, _) = resolve_field::<E>(defs, &a.target, &child(&a.location, "target"), control)?;
        if domain.get(se) != Some(&te.to_owned()) {
            return fail(
                Code::Reference,
                &child(&a.location, "source"),
                "align の両辺は同じ対応表の始域と終域の field",
            );
        }
        if explicit
            .insert(a.source.clone(), a.target.clone())
            .is_some()
        {
            return fail(
                Code::DuplicateId,
                &child(&a.location, "source"),
                "source の align が重複している",
            );
        }
        if !targets.insert(a.target.clone()) {
            return fail(
                Code::DuplicateId,
                &child(&a.location, "target"),
                "target への align が重複している",
            );
        }
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    let mut implicit = Vec::new();
    for (_, e, f) in &maps {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        let es = &defs.declarations[e].signature;
        let fs = &defs.declarations[f].signature;
        let (ep, em) = es.record_fields().expect("owned record");
        let (fp, fm) = fs.record_fields().expect("owned record");
        let source_fields: Vec<_> = ep.iter().chain(em).collect();
        let target_fields: Vec<_> = fp.iter().chain(fm).collect();
        let mut alpha = BTreeMap::new();
        for sf in &source_fields {
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
            let s = format!("{e}.{}", sf.name);
            let t = if let Some(t) = explicit.get(&s) {
                t.clone()
            } else if e == f {
                let t = format!("{f}.{}", sf.name);
                if !targets.insert(t.clone()) {
                    return fail(
                        Code::DuplicateId,
                        &child(&d.location, "name"),
                        format!("`{t}` が同名の対応と align で重複している"),
                    );
                }
                implicit.push((s.clone(), t.clone()));
                t
            } else {
                return fail(
                    Code::Syntax,
                    &child(&d.location, "name"),
                    format!("`{s}` の対応先を align で明記する"),
                );
            };
            alpha.insert(
                sf.name.clone(),
                t.rsplit('.').next().expect("field 完全名").to_owned(),
            );
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        }
        for tf in &target_fields {
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
            let t = format!("{f}.{}", tf.name);
            if !targets.contains(&t) {
                return fail(
                    Code::Syntax,
                    &child(&d.location, "name"),
                    format!("`{t}` への対応元を align で明記する"),
                );
            }
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        }
        for sf in source_fields {
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
            let tf = super::model::find_field_controlled::<E>(
                target_fields.iter().copied(),
                &alpha[&sf.name],
                control,
                Checkpoint::DefinitionSemantics,
            )?
            .expect("解決済み field");
            let moved = transport::<E>(&sf.ty, &mu, &alpha, control)?;
            if (has_reference::<E>(&sf.ty, props, control)?
                || has_reference::<E>(&tf.ty, props, control)?)
                && moved != tf.ty
            {
                return mismatch(
                    &child(&tf.location, "name"),
                    &moved,
                    &tf.ty,
                    format!("`{e}.{}` と `{f}.{}` の型が対応しない", sf.name, tf.name),
                    control,
                );
            }
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        }
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    implicit.sort();
    let d = defs.declarations.get_mut(name).expect("登録済み");
    let PrimitiveSignature::Correspondence {
        from,
        to,
        maps: m,
        implicit: i,
        ..
    } = &mut d.signature
    else {
        unreachable!()
    };
    *from = source;
    *to = target;
    *m = maps;
    *i = implicit;
    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    Ok(())
}
fn resolve_field<'a, E: InputError>(
    defs: &'a CheckedDefinitions,
    name: &'a str,
    at: &Location,
    control: &mut Control,
) -> R<(&'a str, &'a Field), E> {
    E::checkpoint(control, Checkpoint::DefinitionSemantics)?;
    let result = (|| {
        if let Some((owner, field)) = name.rsplit_once('.')
            && let Some(d) = defs.declarations.get(owner)
            && let Some(f) = d.signature.field_controlled::<E>(
                field,
                control,
                Checkpoint::DefinitionSemantics,
            )?
        {
            return Ok((owner, f));
        }
        fail(
            Code::Reference,
            at,
            format!("field `{name}` を解決できない"),
        )
    })();
    E::finish(result, control, Checkpoint::DefinitionSemantics)
}

fn positive_self<E: InputError>(
    t: &Type,
    me: &str,
    positive: bool,
    control: &mut Control,
) -> R<bool, E> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        E::checkpoint(control, Checkpoint::DefinitionData)?;
        let result = match t {
            Type::Data(d) if d == me => positive,
            Type::Tuple(items) => {
                let mut result = true;
                for t in items {
                    E::checkpoint(control, Checkpoint::DefinitionData)?;
                    if !positive_self::<E>(t, me, positive, control)? {
                        result = false;
                        break;
                    }
                    E::checkpoint(control, Checkpoint::DefinitionData)?;
                }
                result
            }
            Type::List(t) | Type::Option(t) => positive_self::<E>(t, me, positive, control)?,
            Type::Set(t) => positive_self::<E>(t, me, false, control)?,
            Type::Map(a, b) => {
                positive_self::<E>(a, me, false, control)?
                    && positive_self::<E>(b, me, false, control)?
            }
            Type::Term(args, ret) => {
                let mut result = true;
                for t in args {
                    E::checkpoint(control, Checkpoint::DefinitionData)?;
                    if !positive_self::<E>(t, me, false, control)? {
                        result = false;
                        break;
                    }
                    E::checkpoint(control, Checkpoint::DefinitionData)?;
                }
                result && positive_self::<E>(ret, me, false, control)?
            }
            _ => true,
        };
        E::checkpoint(control, Checkpoint::DefinitionData)?;
        Ok(result)
    })
}
fn type_inhabited<E: InputError>(
    t: &Type,
    inhabited: &BTreeSet<String>,
    control: &mut Control,
) -> R<bool, E> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        E::checkpoint(control, Checkpoint::DefinitionData)?;
        let result = match t {
            Type::Data(d) => inhabited.contains(d),
            Type::Tuple(items) => {
                let mut result = true;
                for t in items {
                    E::checkpoint(control, Checkpoint::DefinitionData)?;
                    if !type_inhabited::<E>(t, inhabited, control)? {
                        result = false;
                        break;
                    }
                    E::checkpoint(control, Checkpoint::DefinitionData)?;
                }
                result
            }
            _ => true,
        };
        E::checkpoint(control, Checkpoint::DefinitionData)?;
        Ok(result)
    })
}
fn transport<E: InputError>(
    t: &Type,
    mu: &BTreeMap<String, String>,
    alpha: &BTreeMap<String, String>,
    control: &mut Control,
) -> R<Type, E> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        let map = |n: &String| mu.get(n).cloned().unwrap_or_else(|| n.clone());
        let result = match t {
            Type::Ref(n) => Type::Ref(map(n)),
            Type::Owned(n, p) => {
                Type::Owned(map(n), alpha.get(p).cloned().unwrap_or_else(|| p.clone()))
            }
            Type::Tuple(items) => {
                let mut result = Vec::new();
                for t in items {
                    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                    result.push(transport::<E>(t, mu, alpha, control)?);
                    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                }
                Type::Tuple(result)
            }
            Type::List(t) => Type::List(Box::new(transport::<E>(t, mu, alpha, control)?)),
            Type::Set(t) => Type::Set(Box::new(transport::<E>(t, mu, alpha, control)?)),
            Type::Option(t) => Type::Option(Box::new(transport::<E>(t, mu, alpha, control)?)),
            Type::Map(a, b) => Type::Map(
                Box::new(transport::<E>(a, mu, alpha, control)?),
                Box::new(transport::<E>(b, mu, alpha, control)?),
            ),
            t => t.clone(),
        };
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        Ok(result)
    })
}

/// 有向グラフの閉路の一点。自己辺は含まない。
fn find_cycle_controlled<E: InputError>(
    edges: &BTreeMap<String, BTreeSet<String>>,
    control: &mut Control,
) -> R<Option<String>, E> {
    fn visit<E: InputError>(
        n: &str,
        edges: &BTreeMap<String, BTreeSet<String>>,
        state: &mut BTreeMap<String, u8>,
        control: &mut Control,
    ) -> R<Option<String>, E> {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
            match state.get(n) {
                Some(1) => return Ok(Some(n.to_owned())),
                Some(2) => return Ok(None),
                _ => {}
            }
            state.insert(n.to_owned(), 1);
            if let Some(next) = edges.get(n) {
                for m in next {
                    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                    if let Some(c) = visit::<E>(m, edges, state, control)? {
                        return Ok(Some(c));
                    }
                    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                }
            }
            state.insert(n.to_owned(), 2);
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
            Ok(None)
        })
    }
    let mut state = BTreeMap::new();
    for n in edges.keys() {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        if let Some(c) = visit::<E>(n, edges, &mut state, control)? {
            return Ok(Some(c));
        }
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    Ok(None)
}
