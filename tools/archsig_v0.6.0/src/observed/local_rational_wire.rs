use super::*;
use crate::observed::change_result::field_linear_result as field;
pub(super) use crate::observed::change_result::linear_result::{domain, module};
pub(super) fn map(
    b: &mut Builder<'_>,
    source: NodeRef,
    target: NodeRef,
    a: &Matrix,
    n: usize,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    field::map(b, source, target, &integer_fiber::scalars(a), n, c)
}
pub(super) fn vector(
    b: &mut Builder<'_>,
    module: NodeRef,
    values: &[Z],
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    field::vector(
        b,
        module,
        &values.iter().map(Z::scalar).collect::<Vec<_>>(),
        c,
    )
}
// 共通呼出し口。QではSmith証明でなく元の線形系の解または左零化子を返す。
pub(super) fn certificate(
    b: &mut Builder<'_>,
    ring: NodeRef,
    parameters: NodeRef,
    a: &Matrix,
    rhs: &[Z],
    f: &integer_fiber::Fiber,
    dependencies: &[NodeRef],
    c: &mut Control,
) -> Result<(NodeRef, NodeRef), ValidationFailure> {
    let n = f.right.len();
    let equations_module = module(b, ring, a.len(), "free", vec![])?;
    let equations = map(b, parameters, equations_module, a, n, c)?;
    let rhs_ref = vector(b, equations_module, rhs, c)?;
    let mut args = vec![equations, rhs_ref];
    args.extend(dependencies);
    let (kind, data) = if let Some(p) = &f.particular {
        let applied = linear::apply(a, p, c)?;
        if applied != rhs {
            return Err("有理局所解が元の方程式を満たさない".into());
        }
        let point = vector(b, parameters, p, c)?;
        let lhs = vector(b, equations_module, &applied, c)?;
        let recheck = b.proposition(
            "equal",
            vec![lhs, rhs_ref],
            vec![equations, point],
            Decision::Established,
        )?;
        args.extend([point, recheck]);
        (
            "linear_solution",
            Json::obj([
                ("map", equations.wire()),
                ("rhs", rhs_ref.wire()),
                ("solution", point.wire()),
                ("recheck", recheck.wire()),
            ]),
        )
    } else {
        let i = f.obstruction.ok_or("有理局所空解の矛盾行がない")?;
        let annihilator = &f.left[i];
        let zero = integer_fiber::multiply(&vec![annihilator.clone()], a, n, c)?;
        let pairing = linear::apply(&vec![annihilator.clone()], rhs, c)?;
        if zero.iter().flatten().any(|v| !v.is_zero())
            || pairing[0].is_zero()
            || pairing[0] != f.transformed_rhs[i]
        {
            return Err("有理局所空解の左零化子が不正".into());
        }
        let coefficients = vector(b, equations_module, annihilator, c)?;
        let paired = change_result::value(b, &pairing[0].scalar())?;
        args.extend([coefficients, paired]);
        (
            "linear_inconsistent",
            Json::obj([
                ("map", equations.wire()),
                ("rhs", rhs_ref.wire()),
                ("annihilator", coefficients.wire()),
                ("pairing", paired.wire()),
            ]),
        )
    };
    let certificate = b.push(
        NodeType::Evidence,
        "evidence",
        Json::obj([("kind", Json::str(kind)), ("data", data)]),
        args,
        None,
        None,
    )?;
    Ok((equations, certificate))
}
