//! 検査結果の再利用用の保存状態比較。Lawの外延等値とは別の判定である。
use super::*;
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteIteration)?;
    Ok(())
}
pub(super) fn scope(a: &Scope, b: &Scope) -> bool {
    a.readings == b.readings
        && a.snapshots == b.snapshots
        && a.modes == b.modes
        && a.completions == b.completions
        && a.assignments == b.assignments
        && a.quantifiers == b.quantifiers
}
fn option_scope(a: &Option<Scope>, b: &Option<Scope>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => scope(a, b),
        _ => false,
    }
}
fn scalars(a: &[Scalar], b: &[Scalar], c: &Control) -> Result<bool, ValidationFailure> {
    if a.len() != b.len() {
        return Ok(false);
    }
    for (a, b) in a.iter().zip(b) {
        if !scalar(a, b, c)? {
            return Ok(false);
        }
    }
    Ok(true)
}
pub(super) fn scalar(a: &Scalar, b: &Scalar, c: &Control) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        let same = match (a, b) {
            (Scalar::Term(a), Scalar::Term(b)) => a == b,
            (Scalar::Path(a), Scalar::Path(b)) => a.same_program(b, c)?,
            (Scalar::Unit, Scalar::Unit)
            | (Scalar::Text(_), Scalar::Text(_))
            | (Scalar::Z(_), Scalar::Z(_))
            | (Scalar::Q(_, _), Scalar::Q(_, _))
            | (Scalar::Fp { .. }, Scalar::Fp { .. })
            | (Scalar::Bool(_), Scalar::Bool(_))
            | (Scalar::Subject { .. }, Scalar::Subject { .. }) => a == b,
            (
                Scalar::Map {
                    domain: d,
                    codomain: i,
                    pairs: p,
                },
                Scalar::Map {
                    domain: e,
                    codomain: j,
                    pairs: q,
                },
            ) => {
                if d != e || i != j || p.len() != q.len() {
                    false
                } else {
                    let mut same = true;
                    for ((ak, av), (bk, bv)) in p.iter().zip(q) {
                        tick(c)?;
                        if !scalar(ak, bk, c)? || !scalar(av, bv, c)? {
                            same = false;
                            break;
                        }
                        tick(c)?;
                    }
                    same
                }
            }
            (
                Scalar::List {
                    element: e,
                    items: a,
                },
                Scalar::List {
                    element: f,
                    items: b,
                },
            )
            | (
                Scalar::Set {
                    element: e,
                    items: a,
                },
                Scalar::Set {
                    element: f,
                    items: b,
                },
            ) => e == f && scalars(a, b, c)?,
            (
                Scalar::Option {
                    element: e,
                    value: a,
                },
                Scalar::Option {
                    element: f,
                    value: b,
                },
            ) => {
                e == f
                    && match (a, b) {
                        (None, None) => true,
                        (Some(a), Some(b)) => scalar(a, b, c)?,
                        _ => false,
                    }
            }
            (Scalar::Tuple(a), Scalar::Tuple(b)) => scalars(a, b, c)?,
            (
                Scalar::Data {
                    constructor: k,
                    args: a,
                },
                Scalar::Data {
                    constructor: l,
                    args: b,
                },
            ) => k == l && scalars(a, b, c)?,
            _ => false,
        };
        tick(c)?;
        Ok(same)
    })
}
pub(super) fn iteration(
    a: &super::super::call::Iteration,
    b: &super::super::call::Iteration,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    tick(c)?;
    let same = a.caller == b.caller
        && a.source == b.source
        && a.domain == b.domain
        && a.finite == b.finite
        && a.position == b.position
        && a.producer == b.producer
        && match (&a.member, &b.member) {
            (
                super::super::call::Member::ListPosition(a),
                super::super::call::Member::ListPosition(b),
            ) => a == b,
            (
                super::super::call::Member::SetElement(a),
                super::super::call::Member::SetElement(b),
            ) => scalar(a, b, c)?,
            _ => false,
        };
    tick(c)?;
    Ok(same)
}
fn value(a: &SourceValue, b: &SourceValue, c: &Control) -> Result<bool, ValidationFailure> {
    tick(c)?;
    let same = a.comparison == b.comparison
        && a.affine == b.affine
        && match (&a.symbolic, &b.symbolic) {
            (None, None) => true,
            (Some(a), Some(b)) => a.identical(b, c)?,
            _ => false,
        }
        && a.support == b.support
        && scope(&a.scope, &b.scope)
        && option_scope(&a.scalar_scope, &b.scalar_scope)
        && match (&a.known_value, &b.known_value) {
            (None, None) => true,
            (Some(a), Some(b)) => scalar(a, b, c)?,
            _ => false,
        };
    tick(c)?;
    Ok(same)
}
pub(super) fn key(a: &ScopedKey, b: &ScopedKey, c: &Control) -> Result<bool, ValidationFailure> {
    tick(c)?;
    if a.value_read != b.value_read
        || a.expression != b.expression
        || a.reading != b.reading
        || a.context != b.context
        || a.scoped != b.scoped
        || !scope(&a.base, &b.base)
        || a.universal != b.universal
        || a.variables.len() != b.variables.len()
        || a.completions.len() != b.completions.len()
    {
        return Ok(false);
    }
    for ((ak, av), (bk, bv)) in a.variables.iter().zip(&b.variables) {
        if ak != bk || !value(av, bv, c)? {
            return Ok(false);
        }
    }
    for ((af, ar, av), (bf, br, bv)) in a.completions.iter().zip(&b.completions) {
        if af != bf || ar != br || !scalar(av, bv, c)? {
            return Ok(false);
        }
    }
    if let (Some(a), Some(b)) = (&a.universal, &b.universal) {
        if a.completions.len() != b.completions.len() {
            return Ok(false);
        }
        for ((af, av), (bf, bv)) in a.completions.iter().zip(&b.completions) {
            if af != bf || !scalar(av, bv, c)? {
                return Ok(false);
            }
        }
    }
    tick(c)?;
    Ok(true)
}
