//! 有理数の全解を元parameter座標のアフィン空間として公開する。
use super::*;
use crate::observed::{environment::field_change::Linear, numeric};
use archsig_input::law::ast::BinOp;
use linear_result::{Parts, domain, module};
pub(in crate::observed) fn map(
    b: &mut Builder<'_>,
    source: NodeRef,
    target: NodeRef,
    matrix: &crate::observed::field_fiber::Matrix,
    cols: usize,
    c: &Control,
) -> Result<NodeRef, ValidationFailure> {
    let mut columns = vec![];
    let mut args = vec![source, target];
    for j in 0..cols {
        let mut column = vec![];
        for row in matrix {
            c.checkpoint(Checkpoint::PrimitiveValuation)?;
            column.push(value(b, &row[j])?);
        }
        args.extend(&column);
        columns.push(refs(&column));
    }
    b.push(
        NodeType::ModuleMap(source, target),
        "module_map",
        Json::obj([
            ("source", source.wire()),
            ("target", target.wire()),
            ("columns", Json::Arr(columns)),
        ]),
        args,
        None,
        None,
    )
}
pub(in crate::observed) fn vector(
    b: &mut Builder<'_>,
    module: NodeRef,
    items: &[Scalar],
    c: &Control,
) -> Result<NodeRef, ValidationFailure> {
    let mut coordinates = vec![];
    for x in items {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
        coordinates.push(value(b, x)?);
    }
    let mut args = vec![module];
    args.extend(&coordinates);
    b.push(
        NodeType::Vector(module),
        "vector",
        Json::obj([
            ("module", module.wire()),
            ("coordinates", refs(&coordinates)),
        ]),
        args,
        None,
        None,
    )
}

pub(super) fn build(
    b: &mut Builder<'_>,
    linear: &Linear,
    requirements: &[NodeRef],
    c: &Control,
) -> Result<Parts, ValidationFailure> {
    let n = linear.parameter_count;
    let m = linear.equations.len();
    let ring = b.push(
        NodeType::Construction(T::Ring),
        "ring",
        Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str("Q"))]),
        vec![],
        None,
        None,
    )?;
    let pm = module(b, ring, n, "free", vec![])?;
    let sm = module(b, ring, linear.slots.len(), "free", vec![])?;
    let em = module(b, ring, m, "free", vec![])?;
    let parameters = domain(b, pm)?;
    let states = domain(b, sm)?;
    let action_linear = map(b, pm, sm, &linear.action, n, c)?;
    let offset = vector(b, sm, &linear.offset, c)?;
    let action = b.push(
        NodeType::Construction(T::StateMap),
        "state_map",
        Json::obj([
            ("source", parameters.wire()),
            ("target", states.wire()),
            ("kind", Json::str("affine")),
            ("linear", action_linear.wire()),
            ("offset", offset.wire()),
        ]),
        vec![parameters, states, action_linear, offset],
        None,
        None,
    )?;
    let equations = map(b, pm, em, &linear.equations, n, c)?;
    let rhs = vector(b, em, &linear.rhs, c)?;
    let mut args = vec![equations, rhs];
    args.extend(requirements);
    let (certificate, representation, representation_args) = if let Some(p) = &linear.particular {
        let particular = vector(b, pm, p, c)?;
        let mut applied = vec![];
        for row in &linear.equations {
            let mut sum = numeric::zero(&Type::Q, c)?;
            for (x, y) in row.iter().zip(p) {
                sum = numeric::binary(BinOp::Add, &sum, &numeric::binary(BinOp::Mul, x, y, c)?, c)?;
            }
            applied.push(sum);
        }
        if applied != linear.rhs {
            return Err("有理全解の特解が元の線形系を満たさない".into());
        }
        let lhs = vector(b, em, &applied, c)?;
        let recheck = b.proposition(
            "equal",
            vec![lhs, rhs],
            vec![equations, particular],
            Decision::Established,
        )?;
        args.extend([particular, recheck]);
        let certificate = b.push(
            NodeType::Evidence,
            "evidence",
            Json::obj([
                ("kind", Json::str("linear_solution")),
                (
                    "data",
                    Json::obj([
                        ("map", equations.wire()),
                        ("rhs", rhs.wire()),
                        ("solution", particular.wire()),
                        ("recheck", recheck.wire()),
                    ]),
                ),
            ]),
            args,
            None,
            None,
        )?;
        let rank = n - linear.fiber.pivots.len();
        let directions = module(b, ring, rank, "kernel", vec![equations])?;
        let embedding = map(b, directions, pm, &linear.kernel, rank, c)?;
        (
            certificate,
            Json::obj([
                ("kind", Json::str("affine")),
                ("particular", particular.wire()),
                ("directions", directions.wire()),
                ("embedding", embedding.wire()),
            ]),
            vec![particular, directions, embedding],
        )
    } else {
        let row = linear
            .fiber
            .obstruction
            .ok_or("有理不整合の左零化子がない")?;
        let coefficients = &linear.fiber.left[row];
        let zero = numeric::zero(&Type::Q, c)?;
        for column in 0..n {
            let mut sum = zero.clone();
            for (u, equation) in coefficients.iter().zip(&linear.equations) {
                sum = numeric::binary(
                    BinOp::Add,
                    &sum,
                    &numeric::binary(BinOp::Mul, u, &equation[column], c)?,
                    c,
                )?;
            }
            if sum != zero {
                return Err("有理空解の左零化子が元行列を零化しない".into());
            }
        }
        let mut paired = zero.clone();
        for (u, rhs) in coefficients.iter().zip(&linear.rhs) {
            paired = numeric::binary(
                BinOp::Add,
                &paired,
                &numeric::binary(BinOp::Mul, u, rhs, c)?,
                c,
            )?;
        }
        if paired == zero || paired != linear.fiber.transformed_rhs[row] {
            return Err("有理空解の左零化子と元右辺の非零積が不一致".into());
        }
        let annihilator = vector(b, em, coefficients, c)?;
        let pairing = value(b, &paired)?;
        args.extend([annihilator, pairing]);
        let certificate = b.push(
            NodeType::Evidence,
            "evidence",
            Json::obj([
                ("kind", Json::str("linear_inconsistent")),
                (
                    "data",
                    Json::obj([
                        ("map", equations.wire()),
                        ("rhs", rhs.wire()),
                        ("annihilator", annihilator.wire()),
                        ("pairing", pairing.wire()),
                    ]),
                ),
            ]),
            args,
            None,
            None,
        )?;
        (
            certificate,
            Json::obj([
                ("kind", Json::str("empty")),
                ("certificate", certificate.wire()),
            ]),
            vec![certificate],
        )
    };
    Ok(Parts {
        parameters,
        states,
        action,
        certificate,
        representation,
        representation_args,
    })
}
