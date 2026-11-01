// 有限作用から独立した係数型ごとの局所構成。
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
    reading: Option<&integer::linear::Reading>,
    c: &Control,
) -> Result<(NodeRef, NodeRef, State), ValidationFailure> {
    let requirements = selected
        .iter()
        .map(|i| model.requirements[*i].clone())
        .collect::<Vec<_>>();
    let mut pending = change_affine::Pending::default();
    let (matrix, rhs) =
        change_affine::state_equations(env, &model.slots, &requirements, &mut pending)?;
    if !pending.facts.is_empty() {
        return Err(internal!("アフィン方程式の固定位置が欠測している").into());
    }
    if matrix.iter().any(|row| {
        row.iter()
            .enumerate()
            .any(|(i, x)| !x.is_zero() && !indexes.contains(&i))
    }) {
        return Err(internal!("局所アフィン方程式に不可視の座標がある").into());
    }
    let matrix: Matrix = matrix
        .iter()
        .map(|row| indexes.iter().map(|i| row[*i].clone()).collect())
        .collect();
    let (solution, mut domain, mut coefficients, mut fiber) = integer::state::solutions(
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
    let mut ambient = ambient;
    if let Some(reading) = reading {
        let projection: Matrix = reading.map.iter().map(|row| indexes.iter().map(|i| row[*i].clone()).collect()).collect();
        if reading.map.iter().any(|row| row.iter().enumerate().any(|(i,x)| !x.is_zero() && !indexes.contains(&i))) {
            return Err(internal!("アフィン読取りにcontext外の座標がある").into());
        }
        let read_module = wire::module(b, ring, reading.map.len(), "image", vec![solution])?;
        let read_domain = wire::domain(b, read_module)?;
        let quotient = integer::state::affine_map(b, domain, read_domain, ambient, read_module,
            &projection, indexes.len(), &vec![Z::zero(); reading.map.len()], c)?;
        domain = b.push(NodeType::Domain, "domain", Json::obj([
            ("kind", Json::str("image")), ("map", quotient.wire()), ("source", solution.wire()),
        ]), vec![quotient,solution], None, None)?;
        fiber = integer::linear::affine_image(&fiber, &projection, &vec![Z::zero(); reading.map.len()], c)?;
        coefficients = wire::module(b, ring, fiber.rank, "image", vec![quotient])?;
        ambient = read_module;
    }
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
    c: &Control,
) -> Result<NodeRef, ValidationFailure> {
    let Scalar::Tuple(values) = value else {
        return Err(internal!("アフィン状態がTupleでない").into());
    };
    let values = values
        .iter()
        .map(integer::read_coefficient)
        .collect::<Result<Vec<_>, _>>()?;
    let origin = state
        .fiber
        .origin
        .as_ref()
        .ok_or(internal!("有限作用の像を含むアフィンfiberが空か未確定"))?;
    if values.len() != origin.len() { return Err(internal!("アフィン状態の座標数が違う").into()); }
    let delta = values
        .iter()
        .zip(origin)
        .map(|(x, y)| x - y)
        .collect::<Vec<_>>();
    let solution =
        integer_fiber::solve(&state.fiber.basis, state.fiber.rank, &delta, c)?;
    if solution.particular.is_none() {
        return Err(internal!("有限作用の解がアフィン方程式を満たさない").into());
    }
    wire::vector(b, state.ambient, &values, c)
}

pub(super) fn restriction(
    b: &mut Builder<'_>,
    from: &super::State,
    to: &super::State,
    c: &Control,
) -> Result<(NodeRef, NodeRef, Matrix, Matrix), ValidationFailure> {
    let a = from.integer.as_ref().ok_or(internal!("アフィン制限元がない"))?;
    let z = to.integer.as_ref().ok_or(internal!("アフィン制限先がない"))?;
    let projection: Matrix = if let (Some(a), Some(z)) = (&from.reading, &to.reading) { a.restriction(z,c)? } else { to
        .free
        .iter()
        .map(|f| {
            let i = from
                .free
                .iter()
                .position(|x| x == f)
                .ok_or(internal!("アフィン制限先の座標がない"))?;
            Ok((0..from.free.len())
                .map(|j| Z::from(usize::from(i == j)))
                .collect())
        })
        .collect::<Result<_, ValidationFailure>>()? };
    let from_rank = from.reading.as_ref().map_or(from.free.len(), |r|r.map.len());
    let to_rank = to.reading.as_ref().map_or(to.free.len(), |r|r.map.len());
    let image =
        integer_fiber::multiply(&projection, &a.fiber.basis, a.fiber.rank, c)?;
    let coefficients =
        integer::linear::coordinates(&z.fiber.basis, z.fiber.rank, &image, a.fiber.rank, c)?;
    let map = integer::state::affine_map(
        b,
        from.equation_domain,
        to.equation_domain,
        a.ambient,
        z.ambient,
        &projection,
        from_rank,
        &vec![Z::zero(); to_rank],
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
    intersections: &[Vec<usize>],
    contexts: &[NodeRef],
    patches: &[usize],
    cover: NodeRef,
    laws: &[NodeRef],
    coefficients: BTreeMap<(usize, usize), (Matrix, Matrix)>,
    projections: BTreeMap<(usize, usize), Matrix>,
    c: &Control,
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
                        .ok_or(internal!("自由位置がない"))
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let readings = free
        .iter()
        .enumerate()
        .map(|(i,positions)| {
            if let Some(reading) = &states[i].reading { return Ok(reading.clone()); }
            let matrix: Matrix = positions
                .iter()
                .map(|i| {
                    (0..model.slots.len())
                        .map(|j| Z::from(usize::from(*i == j)))
                        .collect()
                })
                .collect();
            integer::linear::Reading::new(&matrix, model.slots.len(), c)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(integer::Diagram {
        equation_only: true,
        slots: model.slots.clone(),
        free,
        readings,
        state_restrictions: projections,
        patches: patches.to_vec(),
        intersections: intersections.to_vec(),
        equation: states
            .iter()
            .map(|s| {
                s.integer
                    .as_ref()
                    .map(|s| s.fiber.clone())
                    .ok_or_else(|| ValidationFailure::from(internal!("アフィンfiberがない")))
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
