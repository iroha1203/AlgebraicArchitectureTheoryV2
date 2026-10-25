//! 局所アフィン集合の像、制限、整数座標。特解を一意な状態と見なさない。
use super::*;
use crate::observed::integer_fiber::{self, Matrix};
use num_bigint::BigInt as Z;
use num_traits::{One, Zero};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Fiber {
    pub origin: Option<Vec<Z>>,
    pub known: bool,
    pub basis: Matrix,
    pub rank: usize,
}
pub(super) fn identity(n: usize) -> Matrix {
    (0..n)
        .map(|i| (0..n).map(|j| Z::from(usize::from(i == j))).collect())
        .collect()
}
pub(super) fn apply(a: &Matrix, x: &[Z], c: &Control) -> Result<Vec<Z>, ValidationFailure> {
    let result = integer_fiber::multiply(a, &x.iter().map(|v| vec![v.clone()]).collect(), 1, c)?;
    Ok(result.into_iter().map(|row| row[0].clone()).collect())
}
pub(super) fn solve(
    a: &Matrix,
    cols: usize,
    rhs: &[Z],
    c: &Control,
) -> Result<Fiber, ValidationFailure> {
    let result = integer_fiber::solve(a, cols, rhs, c)?;
    Ok(Fiber {
        origin: result.particular,
        known: true,
        basis: result.kernel,
        rank: cols - result.rank,
    })
}
pub(super) fn solve_partial(
    a: &Matrix,
    cols: usize,
    rhs: &[Option<Z>],
    c: &Control,
) -> Result<Fiber, ValidationFailure> {
    if let Some(values) = rhs.iter().cloned().collect::<Option<Vec<_>>>() {
        return solve(a, cols, &values, c);
    }
    // 同次核だけを計算する。零右辺を欠測した対象の値には使わない。
    let mut fiber = solve(a, cols, &vec![Z::zero(); a.len()], c)?;
    fiber.origin = None;
    fiber.known = false;
    Ok(fiber)
}
pub(super) fn image(
    a: &Matrix,
    cols: usize,
    c: &Control,
) -> Result<(Matrix, usize), ValidationFailure> {
    let result = integer_fiber::solve(a, cols, &vec![Z::zero(); a.len()], c)?;
    let transformed = integer_fiber::multiply(a, &result.right, cols, c)?;
    Ok((
        transformed
            .into_iter()
            .map(|r| r[..result.rank].to_vec())
            .collect(),
        result.rank,
    ))
}
pub(super) fn coordinates(
    basis: &Matrix,
    rank: usize,
    values: &Matrix,
    cols: usize,
    c: &Control,
) -> Result<Matrix, ValidationFailure> {
    let mut result = vec![vec![Z::zero(); cols]; rank];
    for j in 0..cols {
        c.clone()
            .checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let rhs = values.iter().map(|r| r[j].clone()).collect::<Vec<_>>();
        let fiber = integer_fiber::solve(basis, rank, &rhs, c)?;
        let point = fiber.particular.ok_or("局所制限が係数の像に入らない")?;
        if fiber.rank != rank {
            return Err("局所係数の座標基底が独立でない".into());
        }
        for i in 0..rank {
            result[i][j] = point[i].clone();
        }
    }
    Ok(result)
}
pub(super) fn project(a: &Matrix, positions: &[usize]) -> Matrix {
    positions.iter().map(|i| a[*i].clone()).collect()
}
pub(super) fn restrict(
    from: &Fiber,
    to: &Fiber,
    positions: &[usize],
    c: &Control,
) -> Result<Matrix, ValidationFailure> {
    coordinates(
        &to.basis,
        to.rank,
        &project(&from.basis, positions),
        from.rank,
        c,
    )
}
pub(super) fn affine_image(
    fiber: &Fiber,
    action: &Matrix,
    offset: &[Z],
    c: &Control,
) -> Result<Fiber, ValidationFailure> {
    let matrix = integer_fiber::multiply(action, &fiber.basis, fiber.rank, c)?;
    let (basis, rank) = image(&matrix, fiber.rank, c)?;
    let origin = fiber
        .origin
        .as_ref()
        .map(|p| {
            let mut point = apply(action, p, c)?;
            for (v, offset) in point.iter_mut().zip(offset) {
                *v += offset;
            }
            Ok::<_, ValidationFailure>(point)
        })
        .transpose()?;
    Ok(Fiber {
        origin,
        known: fiber.known,
        basis,
        rank,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Cohomology {
    pub cycles: Matrix,
    pub cycle_rank: usize,
    pub boundary_rank: usize,
    pub projection: Matrix,
    pub torsion: Vec<Z>,
    pub free_rank: usize,
}
pub(super) fn cohomology(
    previous: &Matrix,
    previous_cols: usize,
    next: &Matrix,
    degree_rank: usize,
    c: &Control,
) -> Result<Cohomology, ValidationFailure> {
    let composite = integer_fiber::multiply(next, previous, previous_cols, c)?;
    if composite.iter().flatten().any(|v| !v.is_zero()) {
        return Err("局所複体の連続する微分の合成が零でない".into());
    }
    let cycles = solve(next, degree_rank, &vec![Z::zero(); next.len()], c)?;
    let boundary_coordinates = coordinates(&cycles.basis, cycles.rank, previous, previous_cols, c)?;
    let quotient = integer_fiber::solve(
        &boundary_coordinates,
        previous_cols,
        &vec![Z::zero(); cycles.rank],
        c,
    )?;
    let mut projection = vec![];
    let mut torsion = vec![];
    for i in 0..quotient.rank {
        if quotient.diagonal[i][i] != Z::one() {
            torsion.push(quotient.diagonal[i][i].clone());
            projection.push(quotient.left[i].clone());
        }
    }
    for i in quotient.rank..cycles.rank {
        projection.push(quotient.left[i].clone());
    }
    let boundary_rank = quotient.rank;
    Ok(Cohomology {
        cycles: cycles.basis,
        cycle_rank: cycles.rank,
        boundary_rank,
        projection,
        torsion,
        free_rank: cycles.rank - quotient.rank,
    })
}

pub(super) fn glues(
    diagram: &Diagram,
    sources: &[usize],
    target: usize,
    semantic: bool,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    let states = if semantic {
        &diagram.semantic
    } else {
        &diagram.equation
    };
    if sources.iter().any(|i| states[*i].origin.is_none()) {
        return Ok(states[target].origin.is_none());
    }
    let mut offsets = vec![];
    let mut n = 0;
    for i in sources {
        offsets.push(n);
        n += states[*i].rank;
    }
    let mut equations = vec![];
    let mut rhs = vec![];
    for (a, i) in sources.iter().enumerate() {
        for (b, j) in sources.iter().enumerate().skip(a + 1) {
            c.clone()
                .checkpoint(crate::observed::control::Checkpoint::Localize)?;
            let intersection = diagram.intersections[*i][*j];
            for k in &diagram.free[intersection] {
                let x = diagram.free[*i]
                    .iter()
                    .position(|s| s == k)
                    .ok_or("matchingの位置がない")?;
                let y = diagram.free[*j]
                    .iter()
                    .position(|s| s == k)
                    .ok_or("matchingの位置がない")?;
                let mut row = vec![Z::zero(); n];
                for (l, v) in states[*i].basis[x].iter().enumerate() {
                    row[offsets[a] + l] += v;
                }
                for (l, v) in states[*j].basis[y].iter().enumerate() {
                    row[offsets[b] + l] -= v;
                }
                equations.push(row);
                rhs.push(
                    &states[*j].origin.as_ref().ok_or("局所特解がない")?[y]
                        - &states[*i].origin.as_ref().ok_or("局所特解がない")?[x],
                );
            }
        }
    }
    let matching = solve(&equations, n, &rhs, c)?;
    let Some(point) = &matching.origin else {
        return Ok(states[target].origin.is_none());
    };
    let Some(global) = &states[target].origin else {
        return Ok(false);
    };
    let mut map = vec![];
    let mut origin = vec![];
    for i in sources {
        let positions = diagram.free[*i]
            .iter()
            .map(|k| {
                diagram.free[target]
                    .iter()
                    .position(|j| j == k)
                    .ok_or("全域制限の位置がない")
            })
            .collect::<Result<Vec<_>, _>>()?;
        let projected = project(&states[target].basis, &positions);
        map.extend(coordinates(
            &states[*i].basis,
            states[*i].rank,
            &projected,
            states[target].rank,
            c,
        )?);
        let local = states[*i].origin.as_ref().ok_or("局所特解がない")?;
        let delta = positions
            .iter()
            .enumerate()
            .map(|(j, k)| vec![&global[*k] - &local[j]])
            .collect();
        origin.extend(
            coordinates(&states[*i].basis, states[*i].rank, &delta, 1, c)?
                .into_iter()
                .map(|v| v[0].clone()),
        );
    }
    let relative = coordinates(&matching.basis, matching.rank, &map, states[target].rank, c)?;
    let delta = origin
        .iter()
        .zip(point)
        .map(|(x, y)| x - y)
        .collect::<Vec<_>>();
    let shifted = integer_fiber::solve(&map, states[target].rank, &delta, c)?;
    if shifted.particular.is_none() {
        return Ok(false);
    }
    let image = integer_fiber::solve(
        &relative,
        states[target].rank,
        &vec![Z::zero(); matching.rank],
        c,
    )?;
    Ok(image.rank == matching.rank
        && image.rank == states[target].rank
        && (0..image.rank).all(|i| image.diagonal[i][i] == Z::one()))
}
