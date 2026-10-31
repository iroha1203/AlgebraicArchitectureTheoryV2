use super::*;
pub(in crate::observed::local_result) use crate::observed::environment::change_affine::Pending;
pub(super) struct Guard {
    pub equations: Matrix,
    pub rhs: Vec<Z>,
}
pub(super) struct Linear {
    pub parameter_count: usize,
    pub slots: Vec<Fact>,
    pub action: Matrix,
    pub offset: Vec<Z>,
    pub guard: Option<Guard>,
    pub candidates_empty: bool,
    pub equations: Matrix,
    pub rhs: Vec<Z>,
}
pub(super) fn compute(
    env: &Environment<'_>,
    change: &crate::law::model::Declaration,
    subjects: &[Scalar],
    requirements: &[(String, Vec<(String, Scalar)>)],
    pending: &mut Pending,
) -> Result<Linear, ValidationFailure> {
    let f = crate::observed::environment::field_change::compute(
        env,
        change,
        subjects,
        requirements,
        pending,
    )?;
    Ok(Linear {
        parameter_count: f.parameter_count,
        slots: f.slots,
        action: integer_fiber::matrix(&f.action)?,
        offset: integer_fiber::vector(&f.offset)?,
        guard: Some(Guard {
            equations: integer_fiber::matrix(&f.guard_fiber.reduced)?,
            rhs: integer_fiber::vector(&f.guard_fiber.transformed_rhs)?,
        }),
        candidates_empty: f.guard_fiber.particular.is_none(),
        equations: integer_fiber::matrix(&f.equations)?,
        rhs: integer_fiber::vector(&f.rhs)?,
    })
}
pub(in crate::observed::local_result) fn state_equations(
    env: &Environment<'_>,
    slots: &[Fact],
    requirements: &[(String, Vec<(String, Scalar)>)],
    pending: &mut Pending,
) -> Result<(Matrix, Vec<Option<Z>>), ValidationFailure> {
    let (a, b) = crate::observed::environment::field_change::state_equations(
        env,
        slots,
        requirements,
        pending,
    )?;
    Ok((
        integer_fiber::matrix(&a)?,
        b.iter()
            .map(|v| v.as_ref().map(Z::from_scalar).transpose())
            .collect::<Result<_, _>>()?,
    ))
}
