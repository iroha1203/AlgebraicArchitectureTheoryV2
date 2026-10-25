//! 有限作用とは独立な整数方程式の全fiber。
use super::*;
use crate::observed::change_result::linear_result as wire;
use crate::observed::{environment::change_affine, integer_fiber::Matrix};
use num_bigint::BigInt as Z;
use num_traits::Zero;

pub(super) struct State {
    pub ambient: NodeRef,
    pub coefficients: NodeRef,
    pub fiber: integer::linear::Fiber,
}
pub(super) fn ambient(
    b: &mut Builder<'_>,
    ring: NodeRef,
    n: usize,
) -> Result<(NodeRef, NodeRef), ValidationFailure> {
    let module = wire::module(b, ring, n, "free", vec![])?;
    Ok((module, wire::domain(b, module)?))
}
pub(super) fn solve(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    ring: NodeRef,
    ambient: NodeRef,
    equations: NodeRef,
    model: &finite_model::Model,
    indexes: &[usize],
    selected: &[usize],
    laws: &[NodeRef],
    c: &mut Control,
) -> Result<(NodeRef, NodeRef, State), ValidationFailure> {
    let requirements = selected
        .iter()
        .map(|i| model.requirements[*i].clone())
        .collect::<Vec<_>>();
    let mut pending = change_affine::Pending::default();
    let (matrix, rhs) =
        change_affine::state_equations(env, &model.slots, &requirements, &mut pending)?;
    if !pending.facts.is_empty() {
        return Err("整数方程式の固定位置が欠測している".into());
    }
    if matrix.iter().any(|row| {
        row.iter()
            .enumerate()
            .any(|(i, x)| !x.is_zero() && !indexes.contains(&i))
    }) {
        return Err("局所整数方程式に不可視の座標がある".into());
    }
    let matrix: Matrix = matrix
        .iter()
        .map(|row| indexes.iter().map(|i| row[*i].clone()).collect())
        .collect();
    let (solution, domain, coefficients, fiber) = integer::state::solutions(
        b,
        ring,
        ambient,
        equations,
        &matrix,
        indexes.len(),
        &rhs,
        laws,
        true,
        c,
    )?;
    Ok((
        solution,
        domain,
        State {
            ambient,
            coefficients,
            fiber,
        },
    ))
}
pub(super) fn vector(
    b: &mut Builder<'_>,
    state: &State,
    value: &Scalar,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let Scalar::Tuple(values) = value else {
        return Err("整数状態がTupleでない".into());
    };
    let values = values
        .iter()
        .map(|v| {
            if let Scalar::Z(n) = v {
                Ok(n.clone())
            } else {
                Err(ValidationFailure::from("整数状態の成分がZでない"))
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let origin = state
        .fiber
        .origin
        .as_ref()
        .ok_or("有限作用の像を含む整数fiberが空か未確定")?;
    let delta = values
        .iter()
        .zip(origin)
        .map(|(x, y)| x - y)
        .collect::<Vec<_>>();
    let solution =
        crate::observed::integer_fiber::solve(&state.fiber.basis, state.fiber.rank, &delta, c)?;
    if solution.particular.is_none() {
        return Err("有限作用の解が整数方程式を満たさない".into());
    }
    wire::vector(b, state.ambient, &values, c)
}

pub(super) fn restriction(
    b: &mut Builder<'_>,
    from: &super::State,
    to: &super::State,
    c: &mut Control,
) -> Result<(NodeRef, NodeRef, Matrix, Matrix), ValidationFailure> {
    let a = from.integer.as_ref().ok_or("整数制限元がない")?;
    let z = to.integer.as_ref().ok_or("整数制限先がない")?;
    let projection: Matrix = to
        .free
        .iter()
        .map(|f| {
            let i = from
                .free
                .iter()
                .position(|x| x == f)
                .ok_or("整数制限先の座標がない")?;
            Ok((0..from.free.len())
                .map(|j| Z::from(u8::from(i == j)))
                .collect())
        })
        .collect::<Result<_, ValidationFailure>>()?;
    let image =
        crate::observed::integer_fiber::multiply(&projection, &a.fiber.basis, a.fiber.rank, c)?;
    let coefficients =
        integer::linear::coordinates(&z.fiber.basis, z.fiber.rank, &image, a.fiber.rank, c)?;
    let map = integer::state::affine_map(
        b,
        from.equation_domain,
        to.equation_domain,
        a.ambient,
        z.ambient,
        &projection,
        from.free.len(),
        &vec![Z::zero(); to.free.len()],
        c,
    )?;
    let coefficient_map = wire::map(
        b,
        a.coefficients,
        z.coefficients,
        &coefficients,
        a.fiber.rank,
        c,
    )?;
    Ok((map, coefficient_map, coefficients, projection))
}
pub(super) fn diagram(
    model: &finite_model::Model,
    states: &[super::State],
    supports: &[Support],
    contexts: &[NodeRef],
    patches: &[usize],
    cover: NodeRef,
    laws: &[NodeRef],
    coefficients: BTreeMap<(usize, usize), (Matrix, Matrix)>,
    projections: BTreeMap<(usize, usize), Matrix>,
    c: &mut Control,
) -> Result<integer::Diagram, ValidationFailure> {
    let free = states
        .iter()
        .map(|s| {
            s.free
                .iter()
                .map(|f| {
                    model
                        .slots
                        .iter()
                        .position(|x| x == f)
                        .ok_or("自由位置がない")
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let readings = free
        .iter()
        .map(|positions| {
            let matrix: Matrix = positions
                .iter()
                .map(|i| {
                    (0..model.slots.len())
                        .map(|j| Z::from(u8::from(*i == j)))
                        .collect()
                })
                .collect();
            integer::linear::Reading::new(&matrix, model.slots.len(), c)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let intersections = supports
        .iter()
        .map(|a| {
            supports
                .iter()
                .map(|b| {
                    supports
                        .iter()
                        .position(|x| *x == a.intersect(b))
                        .ok_or("整数contextの交わりがない")
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(integer::Diagram {
        equation_only: true,
        slots: model.slots.clone(),
        free,
        readings,
        state_restrictions: projections,
        patches: patches.to_vec(),
        intersections,
        equation: states
            .iter()
            .map(|s| {
                s.integer
                    .as_ref()
                    .map(|s| s.fiber.clone())
                    .ok_or_else(|| ValidationFailure::from("整数fiberがない"))
            })
            .collect::<Result<Vec<_>, _>>()?,
        semantic: vec![],
        restrictions: coefficients,
        contexts: contexts.to_vec(),
        cover,
        solutions: states.iter().map(|s| [s.equation, s.semantic]).collect(),
        missing: model.missing.clone(),
        requirements: model.requirements.clone(),
        law_refs: laws.to_vec(),
        assignments: model.assignments.clone(),
        sheaf_conditions: vec![],
    })
}
