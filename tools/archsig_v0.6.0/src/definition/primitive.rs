//! 共通原始定義の型適格性・所属・対応・有限 data の検査。
//! 原始署名・Type・実入力位置から直接検査し、解決した構造を同じ表へ保持する。
use super::*;
use crate::{prime::is_prime, types::Type};
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};
type R<T> = Result<T, Box<Issue>>;

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
fn fail<T>(code: Code, at: &Location, message: impl Into<String>) -> R<T> {
    Err(Box::new(Issue {
        code,
        message: message.into(),
        location: at.clone(),
        details: Details::Empty,
    }))
}
fn mismatch<T>(at: &Location, expected: &Type, actual: &Type, message: impl Into<String>) -> R<T> {
    Err(Box::new(Issue {
        code: Code::Type,
        message: message.into(),
        location: at.clone(),
        details: Details::Type {
            expected: expected.erase(),
            actual: actual.erase(),
        },
    }))
}

impl CheckedDefinitions {
    /// data を通じた参照・Term の包含を、原始定義だけから固定点で計算する。
    pub fn data_properties(&self) -> BTreeMap<String, DataProperties> {
        let mut props: BTreeMap<String, DataProperties> = self
            .declarations
            .iter()
            .filter_map(|(n, d)| {
                matches!(d.signature, PrimitiveSignature::Data { .. })
                    .then(|| (n.clone(), DataProperties::default()))
            })
            .collect();
        loop {
            let mut changed = false;
            for (name, d) in &self.declarations {
                let PrimitiveSignature::Data { constructors } = &d.signature else {
                    continue;
                };
                let mut p = DataProperties::default();
                for t in constructors.iter().flat_map(|c| &c.arguments) {
                    p.term_or_path |= has_term_or_path(t, &props);
                    p.reference |= has_reference(t, &props);
                }
                if props[name] != p {
                    props.insert(name.clone(), p);
                    changed = true;
                }
            }
            if !changed {
                return props;
            }
        }
    }
    /// 完全名へ解決済みの原始型を、左にある parameter と実入力位置で検査する。
    pub fn check_primitive_type(
        &self,
        ty: &Type,
        at: &Location,
        earlier: &[(&str, &Type)],
    ) -> R<()> {
        check_type(self, &self.data_properties(), ty, at, earlier)
    }
    pub fn is_root_entity(&self, name: &str) -> bool {
        self.declarations.get(name).is_some_and(|d| {
            matches!(d.signature, PrimitiveSignature::Entity { .. })
                && d.signature.field("owner").is_none()
        })
    }
    /// 原始署名に明記した所属先。検査中にも宣言順に依存せず読める。
    pub fn owner_root(&self, name: &str) -> Option<&str> {
        let d = self.declarations.get(name)?;
        if !matches!(
            d.signature,
            PrimitiveSignature::Entity { .. } | PrimitiveSignature::Arrow { .. }
        ) {
            return None;
        }
        let Type::Ref(root) = &d.signature.field("owner")?.ty else {
            return None;
        };
        self.is_root_entity(root).then_some(root.as_str())
    }
}
fn has_term_or_path(t: &Type, props: &BTreeMap<String, DataProperties>) -> bool {
    t.any(&mut |t| match t {
        Type::Term(..) | Type::Path(..) => true,
        Type::Data(n) => props.get(n).is_some_and(|p| p.term_or_path),
        _ => false,
    })
}
fn has_reference(t: &Type, props: &BTreeMap<String, DataProperties>) -> bool {
    t.any(&mut |t| match t {
        Type::Ref(_) | Type::Owned(..) | Type::Map(..) | Type::Path(..) => true,
        Type::Data(n) => props.get(n).is_some_and(|p| p.reference),
        _ => false,
    })
}
fn check_type(
    defs: &CheckedDefinitions,
    props: &BTreeMap<String, DataProperties>,
    t: &Type,
    at: &Location,
    earlier: &[(&str, &Type)],
) -> R<()> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        check_type_inner(defs, props, t, at, earlier)
    })
}
fn check_type_inner(
    defs: &CheckedDefinitions,
    props: &BTreeMap<String, DataProperties>,
    t: &Type,
    at: &Location,
    earlier: &[(&str, &Type)],
) -> R<()> {
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
                let Some(root) = defs.owner_root(name) else {
                    return fail(
                        Code::Syntax,
                        at,
                        format!("`{name}` は所属先を持たない entity・arrow"),
                    );
                };
                let Some((_, param)) = earlier.iter().find(|(n, _)| *n == index) else {
                    return fail(
                        Code::Reference,
                        &child(at, "2"),
                        format!("添字 `{index}` は左にある parameter を指す"),
                    );
                };
                let expected = Type::Ref(root.into());
                if param.erase() != expected {
                    return mismatch(
                        &child(at, "2"),
                        &expected,
                        param,
                        "添字の parameter は所属先の根 entity の参照",
                    );
                }
            }
        }
        Type::Tuple(items) => {
            for (i, t) in items.iter().enumerate() {
                check_type(defs, props, t, &child(at, &(i + 1).to_string()), earlier)?
            }
        }
        Type::List(t) | Type::Option(t) => check_type(defs, props, t, &child(at, "1"), earlier)?,
        Type::Set(t) => {
            check_type(defs, props, t, &child(at, "1"), earlier)?;
            if has_term_or_path(t, props) {
                return fail(Code::Syntax, at, "Set の要素型は Term・Path を含まない");
            }
        }
        Type::Map(a, b) => {
            check_type(defs, props, a, &child(at, "1"), earlier)?;
            check_type(defs, props, b, &child(at, "2"), earlier)?;
            if a.ref_target().is_none() || b.ref_target().is_none() {
                return fail(Code::Syntax, at, "Map の定義域・値域は参照型");
            }
        }
        Type::Term(args, ret) => {
            let args_at = child(at, "1");
            for (i, t) in args.iter().enumerate() {
                check_type(defs, props, t, &child(&args_at, &i.to_string()), &[])?
            }
            check_type(defs, props, ret, &child(at, "2"), &[])?;
            if args.iter().any(|t| has_reference(t, props)) || has_reference(ret, props) {
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
    Ok(())
}

pub(super) fn check(defs: &mut CheckedDefinitions) -> R<()> {
    let props = defs.data_properties();
    for d in defs.declarations.values() {
        if let Some((parameters, fields)) = d.signature.record_fields() {
            let mut earlier = Vec::new();
            for p in parameters {
                check_type(defs, &props, &p.ty, &child(&p.location, "type"), &earlier)?;
                earlier.push((p.name.as_str(), &p.ty));
            }
            for f in fields {
                check_type(defs, &props, &f.ty, &child(&f.location, "type"), &earlier)?
            }
        } else if let PrimitiveSignature::Data { constructors } = &d.signature {
            for c in constructors {
                let args_at = child(&c.location, "arguments");
                for (i, t) in c.arguments.iter().enumerate() {
                    check_type(defs, &props, t, &child(&args_at, &i.to_string()), &[])?
                }
            }
        }
    }
    // 解決した owner/endpoint は同じ原始表に保持し、reading ごとの複製を作らない。
    let names: Vec<_> = defs.declarations.keys().cloned().collect();
    for name in &names {
        let d = &defs.declarations[name];
        let resolved = match &d.signature {
            PrimitiveSignature::Entity { .. } => {
                let owner = if let Some(f) = d.signature.field("owner") {
                    match &f.ty {
                        Type::Ref(r) if defs.is_root_entity(r) => Some(r.clone()),
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
                    d.signature.field("owner"),
                    d.signature.field("from"),
                    d.signature.field("to"),
                ) else {
                    return fail(
                        Code::Syntax,
                        &child(&d.location, "name"),
                        "arrow は owner・from・to の field を持つ",
                    );
                };
                let root = match &owner.ty {
                    Type::Ref(r) if defs.is_root_entity(r) => r.clone(),
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
                    || defs.owner_root(&endpoint) != Some(root.as_str())
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
    }
    check_data(defs)?;
    for name in names {
        if matches!(
            defs.declarations[&name].signature,
            PrimitiveSignature::Correspondence { .. }
        ) {
            check_correspondence(defs, &props, &name)?
        }
    }
    Ok(())
}

fn check_data(defs: &CheckedDefinitions) -> R<()> {
    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (name, d) in &defs.declarations {
        let PrimitiveSignature::Data { constructors } = &d.signature else {
            continue;
        };
        for c in constructors {
            for (i, t) in c.arguments.iter().enumerate() {
                if !positive_self(t, name, true) {
                    return fail(
                        Code::Syntax,
                        &child(&child(&c.location, "arguments"), &i.to_string()),
                        "data の自己参照は直接または Tuple・List・Option を通る",
                    );
                }
                t.any(&mut |t| {
                    if let Type::Data(other) = t {
                        if other != name {
                            edges.entry(name.clone()).or_default().insert(other.clone());
                        }
                    }
                    false
                });
            }
        }
    }
    if let Some(n) = find_cycle(&edges) {
        return fail(
            Code::Cycle,
            &child(&defs.declarations[&n].location, "name"),
            format!("data `{n}` が相互再帰している"),
        );
    }
    let mut inhabited = BTreeSet::new();
    loop {
        let mut changed = false;
        for (name, d) in &defs.declarations {
            if inhabited.contains(name) {
                continue;
            }
            let PrimitiveSignature::Data { constructors } = &d.signature else {
                continue;
            };
            if constructors
                .iter()
                .any(|c| c.arguments.iter().all(|t| type_inhabited(t, &inhabited)))
            {
                inhabited.insert(name.clone());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (name, d) in &defs.declarations {
        if matches!(d.signature, PrimitiveSignature::Data { .. }) && !inhabited.contains(name) {
            return fail(
                Code::Syntax,
                &child(&d.location, "name"),
                format!("data `{name}` は有限の値を持たない"),
            );
        }
    }
    Ok(())
}
fn owned_types(defs: &CheckedDefinitions, root: &str) -> BTreeSet<String> {
    defs.declarations
        .keys()
        .filter(|n| defs.owner_root(n) == Some(root))
        .cloned()
        .collect()
}
fn check_correspondence(
    defs: &mut CheckedDefinitions,
    props: &BTreeMap<String, DataProperties>,
    name: &str,
) -> R<()> {
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
        parameters.iter().find(|p| p.name == "from"),
        parameters.iter().find(|p| p.name == "to"),
    ) else {
        return fail(
            Code::Syntax,
            &child(&d.location, "name"),
            "correspondence は parameters に from・to を持つ",
        );
    };
    let root = |p: &Field| -> R<String> {
        match &p.ty {
            Type::Ref(n) if defs.is_root_entity(n) => Ok(n.clone()),
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
        if defs.owner_root(&e) != Some(source.as_str())
            || defs.owner_root(&f) != Some(target.as_str())
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
    }
    if domain.keys().cloned().collect::<BTreeSet<_>>() != owned_types(defs, &source)
        || codomain != owned_types(defs, &target)
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
        let (se, _) = resolve_field(defs, &a.source, &child(&a.location, "source"))?;
        let (te, _) = resolve_field(defs, &a.target, &child(&a.location, "target"))?;
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
    }
    let mut implicit = Vec::new();
    for (_, e, f) in &maps {
        let es = &defs.declarations[e].signature;
        let fs = &defs.declarations[f].signature;
        let (ep, em) = es.record_fields().expect("owned record");
        let (fp, fm) = fs.record_fields().expect("owned record");
        let source_fields: Vec<_> = ep.iter().chain(em).collect();
        let target_fields: Vec<_> = fp.iter().chain(fm).collect();
        let mut alpha = BTreeMap::new();
        for sf in &source_fields {
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
        }
        for tf in &target_fields {
            let t = format!("{f}.{}", tf.name);
            if !targets.contains(&t) {
                return fail(
                    Code::Syntax,
                    &child(&d.location, "name"),
                    format!("`{t}` への対応元を align で明記する"),
                );
            }
        }
        for sf in source_fields {
            let tf = target_fields
                .iter()
                .find(|t| t.name == alpha[&sf.name])
                .expect("解決済み field");
            let moved = transport(&sf.ty, &mu, &alpha);
            if (has_reference(&sf.ty, props) || has_reference(&tf.ty, props)) && moved != tf.ty {
                return mismatch(
                    &child(&tf.location, "name"),
                    &moved,
                    &tf.ty,
                    format!("`{e}.{}` と `{f}.{}` の型が対応しない", sf.name, tf.name),
                );
            }
        }
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
    Ok(())
}
fn resolve_field<'a>(
    defs: &'a CheckedDefinitions,
    name: &'a str,
    at: &Location,
) -> R<(&'a str, &'a Field)> {
    if let Some((owner, field)) = name.rsplit_once('.') {
        if let Some(f) = defs
            .declarations
            .get(owner)
            .and_then(|d| d.signature.field(field))
        {
            return Ok((owner, f));
        }
    }
    fail(
        Code::Reference,
        at,
        format!("field `{name}` を解決できない"),
    )
}

fn positive_self(t: &Type, me: &str, positive: bool) -> bool {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        positive_self_inner(t, me, positive)
    })
}

fn positive_self_inner(t: &Type, me: &str, positive: bool) -> bool {
    match t {
        Type::Data(d) if d == me => positive,
        Type::Tuple(items) => items.iter().all(|t| positive_self(t, me, positive)),
        Type::List(t) | Type::Option(t) => positive_self(t, me, positive),
        Type::Set(t) => positive_self(t, me, false),
        Type::Map(a, b) => positive_self(a, me, false) && positive_self(b, me, false),
        Type::Term(args, ret) => {
            args.iter().all(|t| positive_self(t, me, false)) && positive_self(ret, me, false)
        }
        _ => true,
    }
}

fn type_inhabited(t: &Type, inhabited: &BTreeSet<String>) -> bool {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        type_inhabited_inner(t, inhabited)
    })
}

fn type_inhabited_inner(t: &Type, inhabited: &BTreeSet<String>) -> bool {
    match t {
        Type::Data(d) => inhabited.contains(d),
        Type::Tuple(items) => items.iter().all(|t| type_inhabited(t, inhabited)),
        _ => true,
    }
}

fn transport(t: &Type, mu: &BTreeMap<String, String>, alpha: &BTreeMap<String, String>) -> Type {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        transport_inner(t, mu, alpha)
    })
}

fn transport_inner(
    t: &Type,
    mu: &BTreeMap<String, String>,
    alpha: &BTreeMap<String, String>,
) -> Type {
    let map = |n: &String| mu.get(n).cloned().unwrap_or_else(|| n.clone());
    match t {
        Type::Ref(n) => Type::Ref(map(n)),
        Type::Owned(n, p) => {
            Type::Owned(map(n), alpha.get(p).cloned().unwrap_or_else(|| p.clone()))
        }
        Type::Tuple(items) => Type::Tuple(items.iter().map(|t| transport(t, mu, alpha)).collect()),
        Type::List(t) => Type::List(Box::new(transport(t, mu, alpha))),
        Type::Set(t) => Type::Set(Box::new(transport(t, mu, alpha))),
        Type::Option(t) => Type::Option(Box::new(transport(t, mu, alpha))),
        Type::Map(a, b) => Type::Map(
            Box::new(transport(a, mu, alpha)),
            Box::new(transport(b, mu, alpha)),
        ),
        t => t.clone(),
    }
}

/// 有向グラフの閉路の一点。自己辺は含まない。
pub fn find_cycle(edges: &BTreeMap<String, BTreeSet<String>>) -> Option<String> {
    fn visit(
        n: &str,
        edges: &BTreeMap<String, BTreeSet<String>>,
        state: &mut BTreeMap<String, u8>,
    ) -> Option<String> {
        match state.get(n) {
            Some(1) => return Some(n.to_owned()),
            Some(2) => return None,
            _ => {}
        }
        state.insert(n.to_owned(), 1);
        if let Some(next) = edges.get(n) {
            for m in next {
                if let Some(c) = visit(m, edges, state) {
                    return Some(c);
                }
            }
        }
        state.insert(n.to_owned(), 2);
        None
    }
    let mut state = BTreeMap::new();
    for n in edges.keys() {
        if let Some(c) = visit(n, edges, &mut state) {
            return Some(c);
        }
    }
    None
}
