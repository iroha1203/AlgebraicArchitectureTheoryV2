//! 検査済み有限Data値の正規constructor・payloadと、静的に解決済みpatternの照合。
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

#[cfg(test)]
type IterationObserver = Box<dyn FnMut(Span, super::call::Context, &'static str, usize)>;
#[cfg(test)]
thread_local! {
    static EVALUATION_CONTEXT: std::cell::Cell<Option<(Span, super::call::Context)>> = const { std::cell::Cell::new(None) };
    static ITERATION_OBSERVER: std::cell::RefCell<Option<IterationObserver>> = const { std::cell::RefCell::new(None) };
}
#[cfg(test)]
pub(super) fn evaluation_context(
    context: Option<(Span, super::call::Context)>,
) -> Option<(Span, super::call::Context)> {
    EVALUATION_CONTEXT.with(|current| current.replace(context))
}
#[cfg(test)]
pub(super) fn observe_iterations(
    observer: impl FnMut(Span, super::call::Context, &'static str, usize) + 'static,
) {
    ITERATION_OBSERVER.with(|current| *current.borrow_mut() = Some(Box::new(observer)));
}
#[cfg(test)]
pub(super) fn clear_iteration_observer() {
    ITERATION_OBSERVER.with(|current| *current.borrow_mut() = None);
}
#[cfg(test)]
pub(super) fn observe_actual(
    span: Span,
    context: super::call::Context,
    operation: &'static str,
    index: usize,
) {
    ITERATION_OBSERVER.with(|observer| {
        if let Some(observer) = observer.borrow_mut().as_mut() {
            observer(span, context, operation, index);
        }
    });
}
#[cfg(test)]
pub(super) fn observe_iteration(operation: &'static str, index: usize) {
    EVALUATION_CONTEXT.with(|current| {
        if let Some((span, context)) = current.get() {
            ITERATION_OBSERVER.with(|observer| {
                if let Some(observer) = observer.borrow_mut().as_mut() {
                    observer(span, context, operation, index);
                }
            });
        }
    });
}

fn tick(control: &Control) -> Result<(), ValidationFailure> {
    control
        .clone()
        .checkpoint(Checkpoint::FiniteIteration)
        .map_err(ValidationFailure::Stop)
}
pub(super) fn constructors<'a>(
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
                Type::Term(args, ret) => {
                    if !super::term::value_type(ty, control)? {
                        return Ok(false);
                    }
                    for arg in args {
                        if !visit(arg, law, control, active)? {
                            return Ok(false);
                        }
                    }
                    visit(ret, law, control, active)
                }
                Type::Unit | Type::Text | Type::Bool | Type::Ref(_) | Type::Path(..) => Ok(true),
                Type::Map(domain, codomain) => {
                    Ok(domain.ref_target().is_some() && codomain.ref_target().is_some())
                }
                Type::Tuple(items) => {
                    for item in items {
                        tick(control)?;
                        if !visit(item, law, control, active)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                Type::List(item) | Type::Set(item) | Type::Option(item) => {
                    visit(item, law, control, active)
                }
                Type::Data(family) => {
                    if active.contains(family) {
                        // 定義検査済みの正の自己参照。ここでは値の演算が対応するかを
                        // 読むだけで、型の全値域が有限だとは判断しない。実値の有限木は
                        // check/from_inputで辿り、全域の有限性はfiniteが別に検査する。
                        return Ok(true);
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
            Scalar::Path(path) => path.check(control),
            Scalar::Term(t) => t.check(control),
            Scalar::Map { .. } => check_shape(value, control),
            Scalar::Data {
                family,
                constructor: name,
                args,
            } => {
                if !supported(&Type::Data(family.clone()), law, control)? {
                    return Err("未対応Data payloadの生成値".into());
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
            Scalar::Tuple(items) | Scalar::List { items, .. } | Scalar::Set { items, .. } => {
                check_shape(value, control)?;
                if !supported(&value.ty(), law, control)? {
                    return Err("一般値の要素型が未対応".into());
                }
                for item in items {
                    tick(control)?;
                    check(item, law, control)?;
                }
                Ok(())
            }
            Scalar::Option { value: item, .. } => {
                check_shape(value, control)?;
                if !supported(&value.ty(), law, control)? {
                    return Err("Optionの要素型が未対応".into());
                }
                if let Some(item) = item {
                    check(item, law, control)?;
                }
                Ok(())
            }
            _ => check_shape(value, control),
        }
    })
}
/// 内部代入を原始fieldと同じencodingで検査へ渡す。各値を共有Controlで辿る。
pub(super) fn input_json(
    value: &Scalar,
    control: &Control,
) -> Result<crate::canonical::Json, ValidationFailure> {
    use crate::canonical::Json;
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(control)?;
        let children = |items: &[Scalar]| -> Result<Vec<Json>, ValidationFailure> {
            let mut out = Vec::new();
            for item in items {
                tick(control)?;
                out.push(input_json(item, control)?);
            }
            Ok(out)
        };
        let json = match value {
            Scalar::Unit => Json::Arr(vec![]),
            Scalar::Bool(v) => Json::Bool(*v),
            Scalar::Fp { value, .. } => Json::str(value.to_string()),
            Scalar::Subject {
                snapshot, subject, ..
            } => Json::Arr(vec![Json::str(snapshot), Json::str(subject)]),
            Scalar::Map { pairs, .. } => {
                let mut rows = Vec::new();
                for (key, image) in pairs {
                    tick(control)?;
                    rows.push(Json::Arr(vec![
                        input_json(key, control)?,
                        input_json(image, control)?,
                    ]));
                    tick(control)?;
                }
                Json::Arr(rows)
            }
            Scalar::Tuple(items) | Scalar::Set { items, .. } => Json::Arr(children(items)?),
            Scalar::Option { value: None, .. } => Json::obj([("none", Json::Bool(true))]),
            Scalar::Option {
                value: Some(item), ..
            } => Json::obj([("some", input_json(item, control)?)]),
            Scalar::Data {
                constructor, args, ..
            } => Json::obj([
                (
                    "tag",
                    Json::str(
                        constructor
                            .rsplit('.')
                            .next()
                            .ok_or("補完constructorがない")?,
                    ),
                ),
                ("args", Json::Arr(children(args)?)),
            ]),
            _ => return Err("原始有限fieldの補完値でない".into()),
        };
        tick(control)?;
        Ok(json)
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
            (Value::Map(pairs), Type::Map(domain, codomain)) => {
                let domain = domain.erase();
                let codomain = codomain.erase();
                let mut values = Vec::new();
                for (_index, (key, value)) in pairs.iter().enumerate() {
                    #[cfg(test)]
                    observe_iteration("map_input", _index);
                    tick(control)?;
                    let key =
                        from_input(key, &domain, law, control)?.ok_or("Mapの元key型が未対応")?;
                    let value = from_input(value, &codomain, law, control)?
                        .ok_or("Mapの元value型が未対応")?;
                    values.push((key, value));
                    tick(control)?;
                }
                Scalar::Map {
                    domain,
                    codomain,
                    pairs: values,
                }
            }
            (Value::Unit, Type::Unit) => Scalar::Unit,
            (Value::Text(text), Type::Text) => Scalar::Text(text.clone()),
            (Value::Tuple(items), Type::Tuple(types)) => {
                if items.len() != types.len() {
                    return Err("原始Tupleの要素数が違う".into());
                }
                let mut result = Vec::new();
                for (item, ty) in items.iter().zip(types) {
                    tick(control)?;
                    result
                        .push(from_input(item, ty, law, control)?.ok_or("原始Tuple要素が未対応")?);
                }
                Scalar::Tuple(result)
            }
            (Value::List(items), Type::List(element)) | (Value::Set(items), Type::Set(element)) => {
                let mut result = Vec::new();
                for item in items {
                    tick(control)?;
                    result.push(
                        from_input(item, element, law, control)?
                            .ok_or("原始container要素が未対応")?,
                    );
                }
                if matches!(ty, Type::List(_)) {
                    Scalar::List {
                        // 元fieldのowner条件は入力表に保持する。値の型は内側の
                        // Mapと同じ消去型に揃え、空containerでも型を保存する。
                        element: element.erase(),
                        items: result,
                    }
                } else {
                    Scalar::Set {
                        element: element.erase(),
                        items: result,
                    }
                }
            }
            (Value::Option(item), Type::Option(element)) => Scalar::Option {
                element: element.erase(),
                value: item
                    .as_ref()
                    .map(|item| {
                        from_input(item, element, law, control)
                            .and_then(|value| value.ok_or_else(|| "原始Option要素が未対応".into()))
                            .map(Box::new)
                    })
                    .transpose()?,
            },
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
            (Value::Term(t), Type::Term(args, ret)) => Scalar::Term(Box::new(
                super::term::Term::from_input(t, args, ret, control)?,
            )),
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
            (Scalar::Path(a), Scalar::Path(b)) => a == b,
            // 同じ元programならifの両枝で同じ値を保持できる。
            // LawのTerm等値はsupports_binaryで別に判定する。
            (Scalar::Term(a), Scalar::Term(b)) => a == b,
            (Scalar::Map { pairs: a, .. }, Scalar::Map { pairs: b, .. }) => {
                let mut same = a.len() == b.len();
                for (_index, (key, value)) in a.iter().enumerate() {
                    #[cfg(test)]
                    observe_iteration("map_equal", _index);
                    tick(control)?;
                    let mut found = false;
                    for (other_key, other_value) in b {
                        tick(control)?;
                        if equal(key, other_key, control)? {
                            found = equal(value, other_value, control)?;
                            break;
                        }
                    }
                    same &= found;
                    tick(control)?;
                }
                same
            }
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
            (Scalar::Unit, Scalar::Unit) => true,
            (Scalar::Text(a), Scalar::Text(b)) => a == b,
            (Scalar::Tuple(a), Scalar::Tuple(b))
            | (Scalar::List { items: a, .. }, Scalar::List { items: b, .. }) => {
                if a.len() != b.len() {
                    false
                } else {
                    let mut same = true;
                    for (a, b) in a.iter().zip(b) {
                        tick(control)?;
                        same &= equal(a, b, control)?;
                    }
                    same
                }
            }
            (Scalar::Set { items: a, .. }, Scalar::Set { items: b, .. }) => {
                if a.len() != b.len() {
                    false
                } else {
                    let mut same = true;
                    for item in a {
                        tick(control)?;
                        same &= contains(b, item, control)?;
                    }
                    same
                }
            }
            (Scalar::Option { value: a, .. }, Scalar::Option { value: b, .. }) => match (a, b) {
                (None, None) => true,
                (Some(a), Some(b)) => equal(a, b, control)?,
                _ => false,
            },
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
            Scalar::Path(path) => path.check(control),
            Scalar::Term(t) => t.check(control),
            Scalar::Map {
                domain,
                codomain,
                pairs,
            } => {
                if !matches!(domain, Type::Ref(_)) || !matches!(codomain, Type::Ref(_)) {
                    return Err("Mapの両端型が参照でない".into());
                }
                for (index, (key, value)) in pairs.iter().enumerate() {
                    #[cfg(test)]
                    observe_iteration("map_check", index);
                    tick(control)?;
                    if key.ty() != *domain || value.ty() != *codomain {
                        return Err("Mapのkey/value型が違う".into());
                    }
                    check_shape(key, control)?;
                    check_shape(value, control)?;
                    for (previous, _) in &pairs[..index] {
                        tick(control)?;
                        if equal(key, previous, control)? {
                            return Err("Mapに重複keyがある".into());
                        }
                    }
                    tick(control)?;
                }
                Ok(())
            }
            Scalar::Unit | Scalar::Text(_) => Ok(()),
            Scalar::Tuple(items) => {
                for item in items {
                    tick(control)?;
                    check_shape(item, control)?;
                }
                Ok(())
            }
            Scalar::List { element, items } | Scalar::Set { element, items } => {
                if !(if matches!(value, Scalar::Set { .. }) {
                    primitive_type(element, control)?
                } else {
                    super::path_value::result_type(element, control)?
                }) {
                    return Err("containerの要素型が原始対応型でない".into());
                }
                for (index, item) in items.iter().enumerate() {
                    tick(control)?;
                    if &item.ty() != element {
                        return Err("containerの要素型が違う".into());
                    }
                    check_shape(item, control)?;
                    if matches!(value, Scalar::Set { .. })
                        && contains(&items[..index], item, control)?
                    {
                        return Err("Set値に意味上の重複がある".into());
                    }
                }
                Ok(())
            }
            Scalar::Option { element, value } => {
                if !super::path_value::result_type(element, control)? {
                    return Err("Optionの要素型が原始対応型でない".into());
                }
                if let Some(value) = value {
                    if &value.ty() != element {
                        return Err("someの要素型が違う".into());
                    }
                    check_shape(value, control)?;
                }
                Ok(())
            }
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
                    if super::path_value::contains_path(&arg.ty(), control)? {
                        return Err("Dataのpayloadに非原始の結果型がある".into());
                    }
                    check_shape(arg, control)?;
                    tick(control)?;
                }
                Ok(())
            }
            _ => numeric::check(value, control),
        }
    })
}

/// 原始container内で表せる型の形。Dataのsignatureは別に必須照合する。
pub(super) fn primitive_type(ty: &Type, control: &Control) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(control)?;
        match ty {
            Type::Term(..) => super::term::value_type(ty, control),
            Type::Unit
            | Type::Text
            | Type::Bool
            | Type::Z
            | Type::Q
            | Type::Fp(_)
            | Type::Ref(_)
            | Type::Data(_) => Ok(true),
            Type::Map(domain, codomain) => Ok(matches!(domain.as_ref(), Type::Ref(_))
                && matches!(codomain.as_ref(), Type::Ref(_))),
            Type::Tuple(items) => {
                for item in items {
                    tick(control)?;
                    if !primitive_type(item, control)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Type::List(item) | Type::Set(item) | Type::Option(item) => {
                primitive_type(item, control)
            }
            _ => Ok(false),
        }
    })
}
pub(super) fn contains(
    items: &[Scalar],
    item: &Scalar,
    control: &Control,
) -> Result<bool, ValidationFailure> {
    for candidate in items {
        tick(control)?;
        if equal(candidate, item, control)? {
            return Ok(true);
        }
    }
    Ok(false)
}
pub(super) fn set(
    element: Type,
    items: &[Scalar],
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    let mut result = Vec::new();
    let mut remaining = items;
    while let Some((item, rest)) = remaining.split_first() {
        #[cfg(test)]
        observe_iteration("set", items.len() - remaining.len());
        remaining = rest;
        tick(control)?;
        if item.ty() != element {
            return Err("Set構成要素の型が違う".into());
        }
        if !contains(&result, item, control)? {
            result.push(item.clone());
        }
        tick(control)?;
    }
    Ok(Scalar::Set {
        element,
        items: result,
    })
}
pub(super) fn aggregate(
    name: &str,
    value: &Scalar,
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    let (element, items) = match value {
        Scalar::List { element, items } | Scalar::Set { element, items } => (element, items),
        _ => return Err("count/sumの元値がList/Setでない".into()),
    };
    tick(control)?;
    if name == "count" {
        return Ok(Scalar::Z(items.len().into()));
    }
    if name != "sum" {
        return Err("containerの固定演算名が違う".into());
    }
    let mut result = numeric::zero(element, control)?;
    let mut remaining = items.as_slice();
    while let Some((item, rest)) = remaining.split_first() {
        #[cfg(test)]
        observe_iteration("sum", items.len() - remaining.len());
        remaining = rest;
        tick(control)?;
        result = numeric::binary(crate::law::ast::BinOp::Add, &result, item, control)?;
        tick(control)?;
    }
    Ok(result)
}

/// 元の全域表の実keyを照合する。域外は構成不成立であり、像を捏造しない。
pub(super) fn map_apply(
    map: &Scalar,
    key: &Scalar,
    law: &CheckedLaw,
    control: &Control,
) -> Result<Option<Scalar>, ValidationFailure> {
    tick(control)?;
    check(map, law, control)?;
    check(key, law, control)?;
    let Scalar::Map {
        domain,
        codomain,
        pairs,
    } = map
    else {
        return Err("Map適用のcalleeがMap値でない".into());
    };
    if key.ty() != *domain {
        return Err("Map適用の実key型が始域型と違う".into());
    }
    let mut selected = None;
    for (_index, (candidate, image)) in pairs.iter().enumerate() {
        #[cfg(test)]
        observe_iteration("map_lookup", _index);
        tick(control)?;
        if equal(candidate, key, control)? {
            if selected.is_some() || image.ty() != *codomain {
                return Err("Map適用の像が一意・型付きでない".into());
            }
            selected = Some(image.clone());
        }
        tick(control)?;
    }
    tick(control)?;
    Ok(selected)
}
