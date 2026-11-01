//! Lawの数学的等値。元programの同一性検査はvalidation_identityに残す。
use super::{
    data, finite,
    result::{Scalar, ValidationFailure},
    term,
};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::types::Type;
use archsig_input::law::CheckedLaw;
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteIteration)?;
    Ok(())
}
/// 値を受理する型の範囲。有限/アフィン算法の成否は、元の値から別に計算する。
pub(super) fn supported(
    ty: &Type,
    law: &CheckedLaw,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    data::supported(ty, law, c)
}
fn publish(retain: &mut Option<&mut dyn FnMut(Option<bool>)>, answer: Option<bool>) {
    if let Some(retain) = retain.take() {
        retain(answer);
    }
}
fn sequence(
    a: &[Scalar],
    b: &[Scalar],
    law: &CheckedLaw,
    c: &Control,
    retain: &mut Option<&mut dyn FnMut(Option<bool>)>,
) -> Result<Option<bool>, ValidationFailure> {
    if a.len() != b.len() {
        publish(retain, Some(false));
        return Ok(Some(false));
    }
    let mut known = true;
    for (index, (left, right)) in a.iter().zip(b).enumerate() {
        tick(c)?;
        let retaining = retain.is_some();
        let mut completed = |answer| {
            if answer == Some(false) {
                publish(retain, Some(false));
            } else if index + 1 == a.len() {
                publish(retain, (known && answer == Some(true)).then_some(true));
            }
        };
        let answer = if retaining {
            equal_retained(left, right, law, c, &mut completed)?
        } else {
            equal(left, right, law, c)?
        };
        match answer {
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
    equal_with_retained(a, b, law, c, None)
}
/// 完成した数学的比較を、末尾の停止確認より先に保持する。
pub(super) fn equal_retained(
    a: &Scalar,
    b: &Scalar,
    law: &CheckedLaw,
    c: &Control,
    mut retain: impl FnMut(Option<bool>),
) -> Result<Option<bool>, ValidationFailure> {
    equal_with_retained(a, b, law, c, Some(&mut retain))
}
fn equal_with_retained(
    a: &Scalar,
    b: &Scalar,
    law: &CheckedLaw,
    c: &Control,
    mut retain: Option<&mut dyn FnMut(Option<bool>)>,
) -> Result<Option<bool>, ValidationFailure> {
    stacker::maybe_grow(128 * 1024, 1024 * 1024, || {
        tick(c)?;
        if a.ty() != b.ty() {
            return Err("数学的等値の左右型が違う".into());
        }
        if !term::contains(&a.ty(), law, c)? {
            return if let Some(retain) = retain.take() {
                data::equal_retained(a, b, c, |answer| retain(Some(answer))).map(Some)
            } else {
                data::equal(a, b, c).map(Some)
            };
        }
        let answer = match (a, b) {
            (Scalar::Term(a), Scalar::Term(b)) => {
                a.check(c)?;
                b.check(c)?;
                for (_, ty) in &a.params {
                    if !finite::completion_supported(ty, law, c)? {
                        // 非有限域はZ/Q係数から比較し、算法外の同じ元programは保持する。
                        tick(c)?;
                        let compared = term::affine::equal(a, b, law, c)?;
                        let answer = compared.or_else(|| (a == b).then_some(true));
                        publish(&mut retain, answer);
                        return Ok(answer);
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
                        .map(|(a, b)| {
                            if retain.is_some() {
                                equal_retained(&a, &b, law, c, |answer| {
                                    if answer == Some(false) {
                                        publish(&mut retain, Some(false));
                                    } else if _index + 1 == rows.len() {
                                        publish(
                                            &mut retain,
                                            (known && answer == Some(true)).then_some(true),
                                        );
                                    }
                                })
                            } else {
                                equal(&a, &b, law, c)
                            }
                        })
                        .transpose()?
                        .flatten()
                    {
                        Some(false) => {
                            publish(&mut retain, Some(false));
                            return Ok(Some(false));
                        }
                        None => known = false,
                        _ => {}
                    }
                    tick(c)?;
                }
                known.then_some(true)
            }
            (Scalar::Tuple(a), Scalar::Tuple(b))
            | (Scalar::List { items: a, .. }, Scalar::List { items: b, .. }) => {
                sequence(a, b, law, c, &mut retain)?
            }
            (Scalar::Option { value: a, .. }, Scalar::Option { value: b, .. }) => match (a, b) {
                (None, None) => Some(true),
                (Some(a), Some(b)) => equal_with_retained(a, b, law, c, retain.take())?,
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
                    sequence(x, y, law, c, &mut retain)?
                }
            }
            _ => return Err("Termを含む等値の値形が違う".into()),
        };
        publish(&mut retain, answer);
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
