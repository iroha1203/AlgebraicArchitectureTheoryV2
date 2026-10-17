//! Lawの数学的等値。元programの同一性検査はvalidation_identityに残す。
use super::{
    control::{Checkpoint, Control},
    data, finite,
    result::{Scalar, ValidationFailure},
    term,
};
use crate::{law::CheckedLaw, types::Type};
use std::collections::BTreeSet;
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.clone().checkpoint(Checkpoint::FiniteIteration)?;
    Ok(())
}
/// 型から保証できる有限Term比較の範囲。値の構文相違を不等とする判定ではない。
pub(super) fn supported(
    ty: &Type,
    law: &CheckedLaw,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    fn visit(
        t: &Type,
        law: &CheckedLaw,
        c: &Control,
        active: &mut BTreeSet<String>,
    ) -> Result<bool, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            Ok(match t {
                Type::Term(args, ret) => {
                    for a in args {
                        if !finite::completion_supported(a, law, c)? {
                            return Ok(false);
                        }
                    }
                    visit(ret, law, c, active)?
                }
                Type::Tuple(items) => {
                    for t in items {
                        if !visit(t, law, c, active)? {
                            return Ok(false);
                        }
                    }
                    true
                }
                Type::List(t) | Type::Set(t) | Type::Option(t) => visit(t, law, c, active)?,
                Type::Data(name) => {
                    if !active.insert(name.clone()) {
                        return Ok(true);
                    }
                    let result: Result<bool, ValidationFailure> = (|| {
                        for ctor in data::constructors(law, name)? {
                            for t in &ctor.arguments {
                                if !visit(t, law, c, active)? {
                                    return Ok(false);
                                }
                            }
                        }
                        Ok(true)
                    })();
                    active.remove(name);
                    result?
                }
                _ => data::supported(t, law, c)?,
            })
        })
    }
    visit(ty, law, c, &mut BTreeSet::new())
}
fn sequence(
    a: &[Scalar],
    b: &[Scalar],
    law: &CheckedLaw,
    c: &Control,
) -> Result<Option<bool>, ValidationFailure> {
    if a.len() != b.len() {
        return Ok(Some(false));
    }
    let mut known = true;
    for (a, b) in a.iter().zip(b) {
        tick(c)?;
        match equal(a, b, law, c)? {
            Some(false) => return Ok(Some(false)),
            None => known = false,
            _ => {}
        }
    }
    Ok(known.then_some(true))
}
/// Noneは未対応の比較。falseと区別し、構文だけの補完対を生成しない。
pub(super) fn equal(
    a: &Scalar,
    b: &Scalar,
    law: &CheckedLaw,
    c: &Control,
) -> Result<Option<bool>, ValidationFailure> {
    stacker::maybe_grow(128 * 1024, 1024 * 1024, || {
        tick(c)?;
        if a.ty() != b.ty() {
            return Err("数学的等値の左右型が違う".into());
        }
        if !term::contains(&a.ty(), law, c)? {
            return Ok(Some(data::equal(a, b, c)?));
        }
        let answer = match (a, b) {
            (Scalar::Term(a), Scalar::Term(b)) => {
                a.check(c)?;
                b.check(c)?;
                for (_, ty) in &a.params {
                    if !finite::completion_supported(ty, law, c)? {
                        // 非有限域の同じ元programの保持。Lawの二項演算の対応範囲はsupportedが別に決める。
                        tick(c)?;
                        return Ok((a == b).then_some(true));
                    }
                }
                let mut rows = vec![Vec::new()];
                for (_, ty) in &a.params {
                    let values = finite::values(
                        ty,
                        law,
                        c,
                        &mut |_| Err("Term比較に参照族を置けない".into()),
                        &mut |_| {},
                    )?
                    .values;
                    let mut next = Vec::new();
                    for row in &rows {
                        for value in &values {
                            tick(c)?;
                            let mut row = row.clone();
                            row.push(value.clone());
                            next.push(row);
                            tick(c)?;
                        }
                    }
                    rows = next;
                }
                let mut known = true;
                for (_index, row) in rows.iter().enumerate() {
                    #[cfg(test)]
                    data::observe_iteration("term_extensional_case", _index);
                    tick(c)?;
                    let left = a.apply(row, law, c);
                    let left = match left {
                        Ok(v) => Some(v),
                        Err(ValidationFailure::UnsupportedExpression { .. }) => None,
                        Err(e) => return Err(e),
                    };
                    let right = b.apply(row, law, c);
                    let right = match right {
                        Ok(v) => Some(v),
                        Err(ValidationFailure::UnsupportedExpression { .. }) => None,
                        Err(e) => return Err(e),
                    };
                    match left
                        .zip(right)
                        .map(|(a, b)| equal(&a, &b, law, c))
                        .transpose()?
                        .flatten()
                    {
                        Some(false) => return Ok(Some(false)),
                        None => known = false,
                        _ => {}
                    }
                    tick(c)?;
                }
                known.then_some(true)
            }
            (Scalar::Tuple(a), Scalar::Tuple(b))
            | (Scalar::List { items: a, .. }, Scalar::List { items: b, .. }) => {
                sequence(a, b, law, c)?
            }
            (Scalar::Option { value: a, .. }, Scalar::Option { value: b, .. }) => match (a, b) {
                (None, None) => Some(true),
                (Some(a), Some(b)) => equal(a, b, law, c)?,
                _ => Some(false),
            },
            (
                Scalar::Data {
                    constructor: a,
                    args: x,
                    ..
                },
                Scalar::Data {
                    constructor: b,
                    args: y,
                    ..
                },
            ) => {
                if a != b {
                    Some(false)
                } else {
                    sequence(x, y, law, c)?
                }
            }
            _ => return Err("Termを含む等値の値形が違う".into()),
        };
        tick(c)?;
        Ok(answer)
    })
}
pub(super) fn contains(
    items: &[Scalar],
    value: &Scalar,
    law: &CheckedLaw,
    c: &Control,
) -> Result<Option<bool>, ValidationFailure> {
    let mut known = true;
    for item in items {
        tick(c)?;
        match equal(item, value, law, c)? {
            Some(true) => return Ok(Some(true)),
            None => known = false,
            _ => {}
        }
    }
    Ok(known.then_some(false))
}

pub(super) struct AllCases {
    pub value: Option<Scalar>,
    pub pair: Option<(usize, usize)>,
    pub unsupported: bool,
}
pub(super) fn all_cases(
    values: &[Option<&Scalar>],
    law: &CheckedLaw,
    c: &Control,
) -> Result<AllCases, ValidationFailure> {
    let mut same = values.first().is_some_and(Option::is_some);
    let mut unsupported = false;
    if let Some(Some(first)) = values.first() {
        for value in values {
            tick(c)?;
            match value
                .map(|v| equal(first, v, law, c))
                .transpose()?
                .flatten()
            {
                Some(true) => {}
                Some(false) => same = false,
                None => {
                    same = false;
                    unsupported |= value.is_some();
                }
            }
        }
        if same {
            return Ok(AllCases {
                value: Some((*first).clone()),
                pair: None,
                unsupported: false,
            });
        }
    }
    for (i, a) in values.iter().enumerate() {
        for (j, b) in values.iter().enumerate().skip(i + 1) {
            tick(c)?;
            if let Some((a, b)) = a.zip(*b) {
                match equal(a, b, law, c)? {
                    Some(false) => {
                        return Ok(AllCases {
                            value: None,
                            pair: Some((i, j)),
                            unsupported: false,
                        });
                    }
                    None => unsupported = true,
                    _ => {}
                }
            }
        }
    }
    Ok(AllCases {
        value: None,
        pair: None,
        unsupported,
    })
}
