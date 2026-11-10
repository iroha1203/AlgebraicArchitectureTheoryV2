//! 有理半空間の交わり。消去は元の行の非負線形結合を保持する。
use super::{
    field_fiber::{Matrix, inverse},
    numeric,
    result::{Scalar, ValidationFailure},
};
use archsig_common::{
    control::{Checkpoint, Control},
    types::Type,
};
use archsig_input::law::ast::{BinOp, UnOp};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::{cmp::Ordering, collections::BTreeMap};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Halfspace {
    pub coefficients: Vec<Scalar>,
    pub rhs: Scalar,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Row {
    pub inequality: Halfspace,
    pub combination: Vec<Scalar>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Outcome {
    Empty(Row),
    Unique {
        point: Vec<Scalar>,
        bounds: Vec<(Row, Row)>,
    },
    Multiple {
        first: Vec<Scalar>,
        second: Vec<Scalar>,
    },
}

#[derive(Clone)]
struct EliminationRow {
    inequality: Halfspace,
    combination: BTreeMap<usize, Scalar>,
}

impl EliminationRow {
    fn certificate(self, count: usize, c: &Control) -> Result<Row, ValidationFailure> {
        let mut weights = Vec::with_capacity(count);
        for i in 0..count {
            tick(c)?;
            weights.push(
                self.combination
                    .get(&i)
                    .cloned()
                    .unwrap_or_else(|| integer(0)),
            );
        }
        Ok(Row {
            inequality: self.inequality,
            combination: weights,
        })
    }
}

fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::RationalPolyhedron)
        .map_err(Into::into)
}

fn integer(n: i64) -> Scalar {
    Scalar::Q(n.into(), BigInt::one())
}

fn sign(value: &Scalar) -> Result<Ordering, ValidationFailure> {
    let Scalar::Q(n, _) = value else {
        return Err(internal!("半空間の係数がQでない").into());
    };
    Ok(n.cmp(&BigInt::zero()))
}

fn less(a: &Scalar, b: &Scalar, c: &Control) -> Result<bool, ValidationFailure> {
    Ok(numeric::binary(BinOp::Lt, a, b, c)? == Scalar::Bool(true))
}

fn neg(a: &Scalar, c: &Control) -> Result<Scalar, ValidationFailure> {
    numeric::unary(UnOp::Neg, a, c)
}

fn mul(a: &Scalar, b: &Scalar, c: &Control) -> Result<Scalar, ValidationFailure> {
    numeric::binary(BinOp::Mul, a, b, c)
}

fn add(a: &Scalar, b: &Scalar, c: &Control) -> Result<Scalar, ValidationFailure> {
    numeric::binary(BinOp::Add, a, b, c)
}

fn scale_row(
    row: &mut EliminationRow,
    factor: &Scalar,
    c: &Control,
) -> Result<(), ValidationFailure> {
    for x in row
        .inequality
        .coefficients
        .iter_mut()
        .chain(std::iter::once(&mut row.inequality.rhs))
        .chain(row.combination.values_mut())
    {
        *x = mul(x, factor, c)?;
    }
    Ok(())
}

fn combine(
    upper: &EliminationRow,
    lower: &EliminationRow,
    axis: usize,
    c: &Control,
) -> Result<EliminationRow, ValidationFailure> {
    let left = neg(&lower.inequality.coefficients[axis], c)?;
    let right = &upper.inequality.coefficients[axis];
    let pair = |a: &Scalar, b: &Scalar| add(&mul(a, &left, c)?, &mul(b, right, c)?, c);
    let pairs = |a: &[Scalar], b: &[Scalar]| -> Result<Vec<_>, ValidationFailure> {
        a.iter().zip(b).map(|(a, b)| pair(a, b)).collect()
    };
    let mut combination = BTreeMap::new();
    for (row, factor) in [(upper, &left), (lower, right)] {
        for (&position, weight) in &row.combination {
            tick(c)?;
            let contribution = mul(weight, factor, c)?;
            if let Some(previous) = combination.get_mut(&position) {
                *previous = add(previous, &contribution, c)?;
            } else {
                combination.insert(position, contribution);
            }
        }
    }
    Ok(EliminationRow {
        inequality: Halfspace {
            coefficients: pairs(
                &upper.inequality.coefficients,
                &lower.inequality.coefficients,
            )?,
            rhs: pair(&upper.inequality.rhs, &lower.inequality.rhs)?,
        },
        combination,
    })
}

type LeftSide = Vec<(BigInt, BigInt)>;

fn keep_tightest(
    rows: &mut BTreeMap<LeftSide, EliminationRow>,
    mut row: EliminationRow,
    c: &Control,
) -> Result<(), ValidationFailure> {
    tick(c)?;
    let first = row
        .inequality
        .coefficients
        .iter()
        .find(|x| **x != integer(0));
    if let Some(first) = first
        && *first != integer(1)
        && *first != integer(-1)
    {
        let factor = inverse(first, c)?;
        let factor = if sign(&factor)?.is_lt() {
            neg(&factor, c)?
        } else {
            factor
        };
        scale_row(&mut row, &factor, c)?;
    }
    let mut key = Vec::with_capacity(row.inequality.coefficients.len());
    for x in &row.inequality.coefficients {
        tick(c)?;
        let Scalar::Q(n, d) = x else {
            return Err(internal!("半空間の係数がQでない").into());
        };
        key.push((n.clone(), d.clone()));
    }
    if let Some(previous) = rows.get(&key)
        && !less(&row.inequality.rhs, &previous.inequality.rhs, c)?
    {
        return Ok(());
    }
    rows.insert(key, row);
    Ok(())
}

fn eliminate(
    rows: &[EliminationRow],
    axis: usize,
    c: &Control,
) -> Result<Vec<EliminationRow>, ValidationFailure> {
    c.checkpoint(Checkpoint::RationalPolyhedronElimination)?;
    let mut next = BTreeMap::new();
    let mut upper = Vec::new();
    let mut lower = Vec::new();
    for row in rows {
        tick(c)?;
        match sign(&row.inequality.coefficients[axis])? {
            Ordering::Greater => upper.push(row),
            Ordering::Less => lower.push(row),
            Ordering::Equal => keep_tightest(&mut next, row.clone(), c)?,
        }
    }
    // 両側が同じ境界を課す行は等式。各行をその等式で置換すれば、
    // 正負の全対を作らずに同じ射影を得る。組合せ係数は非負のまま保つ。
    let mut equation = None;
    'find: for (i, hi) in upper.iter().enumerate() {
        let negative_rhs = neg(&hi.inequality.rhs, c)?;
        for (j, lo) in lower.iter().enumerate() {
            tick(c)?;
            if lo.inequality.rhs != negative_rhs {
                continue;
            }
            let mut opposite = true;
            for (left, right) in hi
                .inequality
                .coefficients
                .iter()
                .zip(&lo.inequality.coefficients)
            {
                tick(c)?;
                if neg(left, c)? != *right {
                    opposite = false;
                    break;
                }
            }
            if opposite {
                equation = Some((i, j));
                break 'find;
            }
        }
    }
    if let Some((i, j)) = equation {
        for (index, hi) in upper.iter().enumerate() {
            tick(c)?;
            if index != i {
                keep_tightest(&mut next, combine(hi, lower[j], axis, c)?, c)?;
            }
        }
        for (index, lo) in lower.iter().enumerate() {
            tick(c)?;
            if index != j {
                keep_tightest(&mut next, combine(upper[i], lo, axis, c)?, c)?;
            }
        }
    } else {
        for upper in upper {
            for lower in &lower {
                tick(c)?;
                keep_tightest(&mut next, combine(upper, lower, axis, c)?, c)?;
            }
        }
    }
    Ok(next.into_values().collect())
}

fn obstruction(
    rows: &[EliminationRow],
    c: &Control,
) -> Result<Option<EliminationRow>, ValidationFailure> {
    for row in rows {
        tick(c)?;
        if sign(&row.inequality.rhs)?.is_lt()
            && row.inequality.coefficients.iter().all(|v| v == &integer(0))
        {
            return Ok(Some(row.clone()));
        }
    }
    Ok(None)
}

struct Projection {
    rows: Vec<EliminationRow>,
    eliminated: Vec<(usize, Vec<EliminationRow>)>,
}

fn project(
    mut rows: Vec<EliminationRow>,
    axes: impl IntoIterator<Item = usize>,
    c: &Control,
) -> Result<Projection, ValidationFailure> {
    let mut eliminated = Vec::new();
    for axis in axes {
        tick(c)?;
        let next = eliminate(&rows, axis, c)?;
        eliminated.push((axis, rows));
        rows = next;
    }
    Ok(Projection { rows, eliminated })
}

type Bound<'a> = Option<(Scalar, &'a EliminationRow)>;

fn bounds<'a>(
    rows: &'a [EliminationRow],
    axis: usize,
    values: &[Scalar],
    c: &Control,
) -> Result<(Bound<'a>, Bound<'a>), ValidationFailure> {
    let mut low: Bound<'a> = None;
    let mut high: Bound<'a> = None;
    for row in rows {
        tick(c)?;
        let coef = &row.inequality.coefficients[axis];
        let side = sign(coef)?;
        if side.is_eq() {
            continue;
        }
        let mut rhs = row.inequality.rhs.clone();
        for (i, (a, b)) in row.inequality.coefficients.iter().zip(values).enumerate() {
            tick(c)?;
            if i != axis {
                rhs = numeric::binary(BinOp::Sub, &rhs, &mul(a, b, c)?, c)?;
            }
        }
        let at = mul(&rhs, &inverse(coef, c)?, c)?;
        if side.is_lt() {
            if low
                .as_ref()
                .map(|(v, _)| less(v, &at, c))
                .transpose()?
                .unwrap_or(true)
            {
                low = Some((at, row));
            }
        } else if high
            .as_ref()
            .map(|(v, _)| less(&at, v, c))
            .transpose()?
            .unwrap_or(true)
        {
            high = Some((at, row));
        }
    }
    Ok((low, high))
}

fn lift(
    eliminated: &[(usize, Vec<EliminationRow>)],
    mut values: Vec<Scalar>,
    c: &Control,
) -> Result<Vec<Scalar>, ValidationFailure> {
    let zero = integer(0);
    for (axis, rows) in eliminated.iter().rev() {
        let (low, high) = bounds(rows, *axis, &values, c)?;
        values[*axis] = match (low, high) {
            (Some((l, _)), Some((h, _))) if less(&h, &l, c)? => {
                return Err(internal!("半空間の持ち上げの上下限が矛盾する").into());
            }
            (Some((l, _)), _) if less(&zero, &l, c)? => l,
            (_, Some((h, _))) if less(&h, &zero, c)? => h,
            _ => zero.clone(),
        };
    }
    Ok(values)
}

/// 等式を上下両側に置く。この順序を組合せ証拠の座標に使う。
pub(super) fn halfspaces(
    equations: &Matrix,
    rhs: &[Scalar],
    inequalities: &[Halfspace],
    c: &Control,
) -> Result<Vec<Halfspace>, ValidationFailure> {
    if equations.len() != rhs.len() {
        return Err(internal!("半空間へ渡す等式と右辺の件数が違う").into());
    }
    let mut out = Vec::new();
    for (row, b) in equations.iter().zip(rhs) {
        tick(c)?;
        out.push(Halfspace {
            coefficients: row.clone(),
            rhs: b.clone(),
        });
        out.push(Halfspace {
            coefficients: row.iter().map(|x| neg(x, c)).collect::<Result<_, _>>()?,
            rhs: neg(b, c)?,
        });
    }
    for h in inequalities {
        tick(c)?;
        out.push(h.clone());
    }
    Ok(out)
}

pub(super) fn solve(
    original: &[Halfspace],
    n: usize,
    c: &Control,
) -> Result<Outcome, ValidationFailure> {
    let zero = integer(0);
    let one = integer(1);
    let mut tight = BTreeMap::new();
    for (i, h) in original.iter().enumerate() {
        tick(c)?;
        if h.coefficients.len() != n {
            return Err(internal!("半空間の座標数が違う").into());
        }
        for v in h.coefficients.iter().chain([&h.rhs]) {
            if v.ty() != Type::Q {
                return Err(internal!("半空間の係数がQでない").into());
            }
            numeric::check(v, c)?;
        }
        keep_tightest(
            &mut tight,
            EliminationRow {
                inequality: h.clone(),
                combination: BTreeMap::from([(i, one.clone())]),
            },
            c,
        )?;
    }
    let rows = tight.into_values().collect::<Vec<_>>();
    let Projection {
        rows,
        mut eliminated,
    } = project(rows, (0..n).rev(), c)?;
    if let Some(row) = obstruction(&rows, c)? {
        return Ok(Outcome::Empty(row.certificate(original.len(), c)?));
    }
    drop(rows);
    let point = lift(&eliminated, vec![zero.clone(); n], c)?;
    let mut forced = Vec::new();
    for axis in 0..n {
        tick(c)?;
        // Projection onto this axis shares the already eliminated higher axes.
        // Release each no-longer-needed layer as the prefix gets shorter.
        let (next_axis, prefix) = eliminated.pop().ok_or(internal!("射影の消去層がない"))?;
        if next_axis != axis {
            return Err(internal!("射影の消去層が元座標順と違う").into());
        }
        let projected = project(prefix, (0..axis).rev(), c)?;
        let (low, high) = bounds(&projected.rows, axis, &point, c)?;
        if let (Some((l, lrow)), Some((h, hrow))) = (&low, &high)
            && l == h
        {
            forced.push(((*lrow).clone(), (*hrow).clone()));
            continue;
        }
        let alternate = match (low, high) {
            (None, _) => add(&point[axis], &integer(-1), c)?,
            (_, None) => add(&point[axis], &one, c)?,
            (Some((l, _)), Some((h, _))) => {
                if l != point[axis] {
                    l
                } else {
                    h
                }
            }
        };
        let mut pin = vec![zero; n];
        pin[axis] = alternate;
        let second = lift(&projected.eliminated, pin, c)?;
        let second = lift(&eliminated, second, c)?;
        return Ok(Outcome::Multiple {
            first: point,
            second,
        });
    }
    let bounds = forced
        .into_iter()
        .map(|(l, r)| {
            Ok((
                l.certificate(original.len(), c)?,
                r.certificate(original.len(), c)?,
            ))
        })
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    Ok(Outcome::Unique { point, bounds })
}

/// 公開する証拠を消去器と独立に、元の座標と行へ再代入する。
pub(super) fn verify(
    original: &[Halfspace],
    n: usize,
    outcome: &Outcome,
    c: &Control,
) -> Result<(), ValidationFailure> {
    let zero = integer(0);
    let dot = |a: &[Scalar], b: &[Scalar]| -> Result<Scalar, ValidationFailure> {
        if a.len() != b.len() {
            return Err(internal!("有理証拠の座標数が異なる").into());
        }
        let mut value = zero.clone();
        for (a, b) in a.iter().zip(b) {
            tick(c)?;
            value = add(&value, &mul(a, b, c)?, c)?;
        }
        Ok(value)
    };
    let point = |point: &[Scalar]| -> Result<(), ValidationFailure> {
        if point.len() != n {
            return Err(internal!("有理点の座標数が違う").into());
        }
        for h in original {
            tick(c)?;
            if less(&h.rhs, &dot(&h.coefficients, point)?, c)? {
                return Err(internal!("有理証拠の点が元半空間を満たさない").into());
            }
        }
        Ok(())
    };
    let combination = |derived: &Row| -> Result<(), ValidationFailure> {
        if derived.combination.len() != original.len() || derived.inequality.coefficients.len() != n
        {
            return Err(internal!("有理証拠の結合または行の次元が違う").into());
        }
        let mut coefficients = vec![zero.clone(); n];
        let mut rhs = zero.clone();
        for (weight, h) in derived.combination.iter().zip(original) {
            tick(c)?;
            match sign(weight)? {
                Ordering::Less => return Err(internal!("有理証拠の行の重みが負").into()),
                Ordering::Equal => continue,
                Ordering::Greater => {}
            }
            for (sum, coef) in coefficients.iter_mut().zip(&h.coefficients) {
                tick(c)?;
                *sum = add(sum, &mul(weight, coef, c)?, c)?;
            }
            rhs = add(&rhs, &mul(weight, &h.rhs, c)?, c)?;
        }
        if coefficients != derived.inequality.coefficients || rhs != derived.inequality.rhs {
            return Err(internal!("有理証拠の行が元制約の線形結合と異なる").into());
        }
        Ok(())
    };
    match outcome {
        Outcome::Empty(row) => {
            combination(row)?;
            if row.inequality.coefficients.iter().any(|x| x != &zero)
                || !sign(&row.inequality.rhs)?.is_lt()
            {
                return Err(internal!("空な有理解の証拠が矛盾行でない").into());
            }
        }
        Outcome::Unique {
            point: solution,
            bounds,
        } => {
            point(solution)?;
            if bounds.len() != n {
                return Err(internal!("有理解の一意性に必要な座標がない").into());
            }
            for (axis, (lower, upper)) in bounds.iter().enumerate() {
                tick(c)?;
                for (row, expected) in [(lower, Ordering::Less), (upper, Ordering::Greater)] {
                    combination(row)?;
                    let h = &row.inequality;
                    if sign(&h.coefficients[axis])? != expected
                        || h.coefficients
                            .iter()
                            .enumerate()
                            .any(|(i, x)| i != axis && x != &zero)
                        || dot(&h.coefficients, solution)? != h.rhs
                    {
                        return Err(internal!("有理解の座標を固定する上下限が違う").into());
                    }
                }
            }
        }
        Outcome::Multiple { first, second } => {
            point(first)?;
            point(second)?;
            if first == second {
                return Err(internal!("有理解の非一意性に異なる二点がない").into());
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_bounds_distinguish_empty_singleton_and_multiple() {
        let c = Control::unlimited();
        let one_third = Scalar::Q(1.into(), 3.into());
        let negative_third = Scalar::Q((-1).into(), 3.into());
        let mut rows = vec![
            Halfspace {
                coefficients: vec![integer(-1)],
                rhs: negative_third,
            },
            Halfspace {
                coefficients: vec![integer(1)],
                rhs: one_third.clone(),
            },
        ];
        let Outcome::Unique { point, bounds } = solve(&rows, 1, &c).unwrap() else {
            panic!("equal closed bounds force one value");
        };
        assert_eq!(point, [one_third.clone()]);
        assert_eq!(bounds[0].0.combination, [integer(1), integer(0)]);
        assert_eq!(bounds[0].1.combination, [integer(0), integer(1)]);

        rows[1].rhs = Scalar::Q(99997.into(), 300000.into()); // 1/3 - 1/100000
        let Outcome::Empty(row) = solve(&rows, 1, &c).unwrap() else {
            panic!("an exact shortage makes the intersection empty");
        };
        assert_eq!(row.inequality.coefficients, [integer(0)]);
        assert_eq!(row.inequality.rhs, Scalar::Q((-1).into(), 100000.into()));
        assert_eq!(row.combination, [integer(1), integer(1)]);

        rows[1].rhs = integer(1);
        let Outcome::Multiple { first, second } = solve(&rows, 1, &c).unwrap() else {
            panic!("a genuine interval has distinct witnesses");
        };
        assert_eq!(first, [one_third]);
        assert_eq!(second, [integer(1)]);
    }
}
