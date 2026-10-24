//! 整数全解の型付き表示。表示の特解を唯一のAssignmentとして選ばない。
use super::*;
use crate::observed::{environment::change_affine::Linear, integer_fiber::Matrix};
use num_bigint::BigInt as Z;
use num_traits::Zero;

pub(super) struct Parts {
    pub parameters: NodeRef,
    pub states: NodeRef,
    pub action: NodeRef,
    pub certificate: NodeRef,
    pub representation: Json,
    pub representation_args: Vec<NodeRef>,
}
fn module(
    b: &mut Builder<'_>,
    ring: NodeRef,
    n: usize,
    name: &str,
    arguments: Vec<NodeRef>,
) -> Result<NodeRef, ValidationFailure> {
    let mut args = vec![ring];
    args.extend(&arguments);
    b.push(
        NodeType::Construction(T::Module),
        "module",
        Json::obj([
            ("ring", ring.wire()),
            (
                "generators",
                Json::Arr(
                    (0..n)
                        .map(|i| {
                            Json::obj([
                                ("type", Type::Text.wire()),
                                ("value", Json::str(format!("e{i}"))),
                            ])
                        })
                        .collect(),
                ),
            ),
            ("relations", Json::Arr(vec![])),
            ("free_rank", Json::Nat(n as u64)),
            ("torsion", Json::Arr(vec![])),
            (
                "construction",
                Json::obj([("name", Json::str(name)), ("arguments", refs(&arguments))]),
            ),
        ]),
        args,
        None,
        None,
    )
}
fn map(
    b: &mut Builder<'_>,
    source: NodeRef,
    target: NodeRef,
    matrix: &Matrix,
    cols: usize,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let mut columns = vec![];
    let mut args = vec![source, target];
    for j in 0..cols {
        let mut column = vec![];
        for row in matrix {
            c.checkpoint(Checkpoint::PrimitiveValuation)?;
            column.push(value(b, &Scalar::Z(row[j].clone()))?);
        }
        args.extend(&column);
        columns.push(refs(&column));
    }
    b.push(
        NodeType::ModuleMap(source,target),
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
fn vector(
    b: &mut Builder<'_>,
    module: NodeRef,
    items: &[Z],
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let mut coordinates = vec![];
    for x in items {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
        coordinates.push(value(b, &Scalar::Z(x.clone()))?);
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
fn domain(b: &mut Builder<'_>, module: NodeRef) -> Result<NodeRef, ValidationFailure> {
    b.push(
        NodeType::Domain,
        "domain",
        Json::obj([("kind", Json::str("module")), ("module", module.wire())]),
        vec![module],
        None,
        None,
    )
}
pub(super) fn build(
    b: &mut Builder<'_>,
    linear: &Linear,
    requirements: &[NodeRef],
    c: &mut Control,
) -> Result<Parts, ValidationFailure> {
    let n = linear.fiber.right.len();
    let m = linear.equations.len();
    let ring = b.push(
        NodeType::Construction(T::Ring),
        "ring",
        Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str("Z"))]),
        vec![],
        None,
        None,
    )?;
    let parameter_module = module(b, ring, n, "free", vec![])?;
    let state_module = module(b, ring, linear.slots.len(), "free", vec![])?;
    let equation_module = module(b, ring, m, "free", vec![])?;
    let parameters = domain(b, parameter_module)?;
    let states = domain(b, state_module)?;
    let action_linear = map(b, parameter_module, state_module, &linear.action, n, c)?;
    let offset = vector(b, state_module, &linear.offset, c)?;
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
    let equations = map(
        b,
        parameter_module,
        equation_module,
        &linear.equations,
        n,
        c,
    )?;
    let left = map(
        b,
        equation_module,
        equation_module,
        &linear.fiber.left,
        m,
        c,
    )?;
    let right = map(
        b,
        parameter_module,
        parameter_module,
        &linear.fiber.right,
        n,
        c,
    )?;
    let diagonal = map(
        b,
        parameter_module,
        equation_module,
        &linear.fiber.diagonal,
        n,
        c,
    )?;
    let rhs = vector(b, equation_module, &linear.rhs, c)?;
    let transformed = vector(b, equation_module, &linear.fiber.transformed_rhs, c)?;
    let mut divisibility = vec![];
    for i in 0..m {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
        let divisor = if i < linear.fiber.rank {
            linear.fiber.diagonal[i][i].clone()
        } else {
            Z::zero()
        };
        let dividend = &linear.fiber.transformed_rhs[i];
        let holds = if divisor.is_zero() {
            dividend.is_zero()
        } else {
            (dividend % &divisor).is_zero()
        };
        let a = value(b, &Scalar::Z(divisor))?;
        let d = value(b, &Scalar::Z(dividend.clone()))?;
        divisibility.push(b.proposition(
            "divides",
            vec![a, d],
            vec![equations, left, right, diagonal, rhs],
            if holds {
                Decision::Established
            } else {
                Decision::Refuted
            },
        )?);
    }
    let mut args = vec![equations, left, right, diagonal, rhs, transformed];
    args.extend(&divisibility);
    args.extend(requirements);
    let certificate = b.push(
        NodeType::Evidence,
        "evidence",
        Json::obj([
            ("kind", Json::str("smith")),
            (
                "data",
                Json::obj([
                    ("map", equations.wire()),
                    ("left", left.wire()),
                    ("right", right.wire()),
                    ("diagonal", diagonal.wire()),
                    ("transformed_rhs", transformed.wire()),
                    ("divisibility", refs(&divisibility)),
                ]),
            ),
        ]),
        args,
        None,
        None,
    )?;
    let (representation, representation_args) = if let Some(p) = &linear.fiber.particular {
        let particular = vector(b, parameter_module, p, c)?;
        let directions = module(b, ring, n - linear.fiber.rank, "kernel", vec![equations])?;
        let embedding = map(
            b,
            directions,
            parameter_module,
            &linear.fiber.kernel,
            n - linear.fiber.rank,
            c,
        )?;
        (
            Json::obj([
                ("kind", Json::str("affine")),
                ("particular", particular.wire()),
                ("directions", directions.wire()),
                ("embedding", embedding.wire()),
            ]),
            vec![particular, directions, embedding],
        )
    } else {
        (
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
