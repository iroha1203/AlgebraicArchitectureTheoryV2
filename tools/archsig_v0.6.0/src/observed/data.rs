//! 非再帰Dataの正規constructor・payloadと、静的に解決済みpatternの照合。
use super::{
    control::{Checkpoint, Control},
    numeric,
    result::{Scalar, ValidationFailure},
};
use crate::{
    archmap::Value,
    definition::{Constructor, PrimitiveSignature},
    law::{
        CheckedLaw,
        ast::{ExprKind, Pattern, Span},
    },
    types::Type,
};
use std::collections::BTreeMap;

fn tick(control: &Control) -> Result<(), ValidationFailure> {
    control
        .clone()
        .checkpoint(Checkpoint::FiniteIteration)
        .map_err(ValidationFailure::Stop)
}
fn constructors<'a>(
    law: &'a CheckedLaw,
    family: &str,
) -> Result<&'a [Constructor], ValidationFailure> {
    match &law
        .definitions
        .declarations
        .get(family)
        .ok_or("Data定義がない")?
        .signature
    {
        PrimitiveSignature::Data { constructors } => Ok(constructors),
        _ => Err("Data familyがData定義でない".into()),
    }
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
                Type::Bool | Type::Ref(_) => Ok(true),
                Type::Data(family) => {
                    if active.contains(family) {
                        return Ok(false);
                    }
                    active.push(family.clone());
                    let result = (|| {
                        for ctor in constructors(law, family)? {
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
                _ => numeric::is_numeric_type(ty, control),
            }
        })
    }
    visit(ty, law, control, &mut vec![])
}
pub(super) fn constructor<'a>(
    law: &'a CheckedLaw,
    family: &str,
    name: &str,
    control: &Control,
) -> Result<&'a Constructor, ValidationFailure> {
    for ctor in constructors(law, family)? {
        tick(control)?;
        if format!("{family}.{}", ctor.name) == name {
            return Ok(ctor);
        }
    }
    Err("正規constructorが元familyにない".into())
}
pub(super) fn resolved(
    law: &CheckedLaw,
    span: Span,
    control: &Control,
) -> Result<Option<String>, ValidationFailure> {
    let mut found = None;
    for info in &law.infos {
        tick(control)?;
        for (at, target) in &info.references {
            tick(control)?;
            if *at == span
                && let Some((family, _)) = target.rsplit_once('.')
                && matches!(
                    law.definitions
                        .declarations
                        .get(family)
                        .map(|d| &d.signature),
                    Some(PrimitiveSignature::Data { .. })
                )
            {
                constructor(law, family, target, control)?;
                if found.as_ref().is_some_and(|previous| previous != target) {
                    return Err("constructor静的解決が一意でない".into());
                }
                found = Some(target.clone());
            }
        }
    }
    Ok(found)
}
pub(super) fn expression(
    law: &CheckedLaw,
    id: usize,
    control: &Control,
) -> Result<Option<(String, Vec<usize>)>, ValidationFailure> {
    let (mut name, args) = match &law.exprs[id].kind {
        ExprKind::Call { callee, args } => (*callee, args.clone()),
        ExprKind::Dotted(_) => (id, vec![]),
        _ => return Ok(None),
    };
    while let ExprKind::Group(inner) = law.exprs[name].kind {
        tick(control)?;
        name = inner;
    }
    let Some(target) = resolved(law, law.exprs[name].span, control)? else {
        return Ok(None);
    };
    let Type::Data(family) = law.expr_type(id).ok_or("constructor元型がない")? else {
        return Err("constructor元型がDataでない".into());
    };
    let ctor = constructor(law, family, &target, control)?;
    if args.len() != ctor.arguments.len() {
        return Err("constructor元arityが違う".into());
    }
    for (&arg, ty) in args.iter().zip(&ctor.arguments) {
        tick(control)?;
        if law.expr_type(arg) != Some(ty) {
            return Err("constructor元payload型が違う".into());
        }
    }
    Ok(Some((target, args)))
}
pub(super) fn check(
    value: &Scalar,
    law: &CheckedLaw,
    control: &Control,
) -> Result<(), ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(control)?;
        match value {
            Scalar::Data {
                family,
                constructor: name,
                args,
            } => {
                if !supported(&Type::Data(family.clone()), law, control)? {
                    return Err("未対応Data payload・再帰型の生成値".into());
                }
                let ctor = constructor(law, family, name, control)?;
                if args.len() != ctor.arguments.len() {
                    return Err("Data値のarityが違う".into());
                }
                for (arg, ty) in args.iter().zip(&ctor.arguments) {
                    tick(control)?;
                    if &arg.ty() != ty {
                        return Err("Data値のpayload型が違う".into());
                    }
                    check(arg, law, control)?;
                }
                Ok(())
            }
            _ => numeric::check(value, control),
        }
    })
}
pub(super) fn from_input(
    value: &Value,
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
) -> Result<Option<Scalar>, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(control)?;
        if !supported(ty, law, control)? {
            return Ok(None);
        }
        let result = match (value, ty) {
            (
                Value::Data {
                    constructor: name,
                    args,
                },
                Type::Data(family),
            ) => {
                let ctor = constructor(law, family, name, control)?;
                if args.len() != ctor.arguments.len() {
                    return Err("原始Dataのarityが違う".into());
                }
                let mut values = Vec::new();
                for (arg, ty) in args.iter().zip(&ctor.arguments) {
                    tick(control)?;
                    values.push(
                        from_input(arg, ty, law, control)?.ok_or("対応Dataのpayload値がない")?,
                    );
                }
                Scalar::Data {
                    family: family.clone(),
                    constructor: name.clone(),
                    args: values,
                }
            }
            (Value::Bool(b), Type::Bool) => Scalar::Bool(*b),
            (Value::Ref { snapshot, subject }, Type::Ref(entity)) => Scalar::Subject {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                entity: entity.clone(),
            },
            _ => return numeric::from_input(value, ty, control),
        };
        check(&result, law, control)?;
        Ok(Some(result))
    })
}
/// 名前binderの型と元scrutineeからのconstructor引数位置。値の存在を仮定しない。
#[derive(Clone, Debug)]
pub(super) struct Binder {
    pub name: String,
    pub ty: Type,
    pub path: Vec<usize>,
}
pub(super) fn binders(
    pattern: &Pattern,
    ty: &Type,
    law: &CheckedLaw,
    control: &Control,
) -> Result<Vec<Binder>, ValidationFailure> {
    fn walk(
        pattern: &Pattern,
        ty: &Type,
        path: &mut Vec<usize>,
        out: &mut Vec<Binder>,
        law: &CheckedLaw,
        control: &Control,
    ) -> Result<(), ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(control)?;
            let (span, args) = match pattern {
                Pattern::Wild(_) => return Ok(()),
                Pattern::Name(name) => {
                    if resolved(law, name.span, control)?.is_none() {
                        out.push(Binder {
                            name: name.name.clone(),
                            ty: ty.clone(),
                            path: path.clone(),
                        });
                        return Ok(());
                    }
                    (name.span, &[][..])
                }
                Pattern::Ctor { name, args, .. } => (name.span(), args.as_slice()),
            };
            let target = resolved(law, span, control)?.ok_or("pattern正規constructorがない")?;
            let Type::Data(family) = ty else {
                return Err("constructor pattern型がDataでない".into());
            };
            let ctor = constructor(law, family, &target, control)?;
            if ctor.arguments.len() != args.len() {
                return Err("pattern元arityが違う".into());
            }
            for (index, (arg, ty)) in args.iter().zip(&ctor.arguments).enumerate() {
                path.push(index);
                let result = walk(arg, ty, path, out, law, control);
                path.pop();
                result?;
            }
            Ok(())
        })
    }
    let mut result = vec![];
    walk(pattern, ty, &mut vec![], &mut result, law, control)?;
    Ok(result)
}
pub(super) fn matches(
    pattern: &Pattern,
    value: &Scalar,
    law: &CheckedLaw,
    control: &Control,
) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(control)?;
        let (span, patterns) = match pattern {
            Pattern::Wild(_) => return Ok(true),
            Pattern::Name(name) => match resolved(law, name.span, control)? {
                None => return Ok(true),
                Some(_) => (name.span, &[][..]),
            },
            Pattern::Ctor { name, args, .. } => (name.span(), args.as_slice()),
        };
        let target = resolved(law, span, control)?.ok_or("patternの静的constructorがない")?;
        let Scalar::Data {
            constructor, args, ..
        } = value
        else {
            return Err("constructor照合値がDataでない".into());
        };
        if constructor != &target {
            return Ok(false);
        }
        if args.len() != patterns.len() {
            return Err("patternと実Dataのarityが違う".into());
        }
        for (p, value) in patterns.iter().zip(args) {
            if !matches(p, value, law, control)? {
                return Ok(false);
            }
        }
        Ok(true)
    })
}
pub(super) fn select(
    law: &CheckedLaw,
    id: usize,
    value: Option<&Scalar>,
    control: &Control,
) -> Result<Option<usize>, ValidationFailure> {
    let ExprKind::Match { arms, .. } = &law.exprs[id].kind else {
        return Err("選択元がmatchでない".into());
    };
    let Some(value) = value else {
        return Ok(None);
    };
    check(value, law, control)?;
    for (index, arm) in arms.iter().enumerate() {
        tick(control)?;
        if matches(&arm.pattern, value, law, control)? {
            return Ok(Some(index));
        }
    }
    Err("既知matchに選択armがない".into())
}
pub(super) fn project(
    value: &Scalar,
    path: &[usize],
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    let mut value = value;
    for &index in path {
        tick(control)?;
        let Scalar::Data { args, .. } = value else {
            return Err("binder path中間値がDataでない".into());
        };
        value = args.get(index).ok_or("binder pathがarity外")?;
    }
    Ok(value.clone())
}
pub(super) fn bindings(
    law: &CheckedLaw,
    id: usize,
    arm: usize,
    value: &Scalar,
    control: &Control,
) -> Result<BTreeMap<String, Scalar>, ValidationFailure> {
    let ExprKind::Match { scrutinee, arms } = &law.exprs[id].kind else {
        return Err("binder元がmatchでない".into());
    };
    let mut result = BTreeMap::new();
    for binder in binders(
        &arms.get(arm).ok_or("binder armがない")?.pattern,
        law.expr_type(*scrutinee).ok_or("scrutinee型がない")?,
        law,
        control,
    )? {
        let projected = project(value, &binder.path, control)?;
        if projected.ty() != binder.ty || result.insert(binder.name, projected).is_some() {
            return Err("binder名・投影型が元patternと違う".into());
        }
    }
    Ok(result)
}

/// Dataの構造等値。constructor引数ごとの照合でも元の停止制御を通す。
pub(super) fn equal(
    left: &Scalar,
    right: &Scalar,
    control: &Control,
) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(control)?;
        if left.ty() != right.ty() {
            return Err("構造等値の元型が違う".into());
        }
        let equal = match (left, right) {
            (
                Scalar::Data {
                    family: a,
                    constructor: b,
                    args: c,
                },
                Scalar::Data {
                    family: d,
                    constructor: e,
                    args: f,
                },
            ) => {
                if a != d || b != e {
                    false
                } else {
                    if c.len() != f.len() {
                        return Err("同constructorのarityが違う".into());
                    }
                    let mut same = true;
                    for (left, right) in c.iter().zip(f) {
                        tick(control)?;
                        same &= equal(left, right, control)?;
                        tick(control)?;
                    }
                    same
                }
            }
            (Scalar::Bool(a), Scalar::Bool(b)) => a == b,
            (
                Scalar::Subject {
                    snapshot: a,
                    subject: b,
                    entity: c,
                },
                Scalar::Subject {
                    snapshot: d,
                    subject: e,
                    entity: f,
                },
            ) => a == d && b == e && c == f,
            _ => {
                numeric::binary(crate::law::ast::BinOp::Eq, left, right, control)?
                    == Scalar::Bool(true)
            }
        };
        tick(control)?;
        Ok(equal)
    })
}

/// Graph単体では一般値の形を検査する。familyの定義・arity・payload型はEnvironmentで照合する。
pub(super) fn check_shape(value: &Scalar, control: &Control) -> Result<(), ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(control)?;
        match value {
            Scalar::Data {
                family,
                constructor,
                args,
            } => {
                let name = constructor
                    .strip_prefix(family)
                    .and_then(|suffix| suffix.strip_prefix('.'));
                if family.is_empty()
                    || name.is_none_or(|name| name.is_empty() || name.contains('.'))
                {
                    return Err("Data値のfamily・正規constructor形式が違う".into());
                }
                for arg in args {
                    tick(control)?;
                    check_shape(arg, control)?;
                    tick(control)?;
                }
                Ok(())
            }
            _ => numeric::check(value, control),
        }
    })
}
