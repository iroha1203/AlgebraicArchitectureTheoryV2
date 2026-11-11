//! 有理数の全解を元parameter座標のアフィン空間として公開する。
use super::*;
use crate::observed::{
    environment::field_change::{Linear, Solutions},
    numeric,
};
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
    )
}

pub(super) fn materialize_quantifiers(
    b: &mut Builder<'_>,
    domains: &[(Quantifier, Vec<Scalar>)],
    requirements: &[NodeRef],
    c: &Control,
) -> Result<Vec<Quantifier>, ValidationFailure> {
    let mut quantifiers = Vec::new();
    let mut known = BTreeMap::<((usize, usize), usize), Vec<(&[Scalar], NodeRef)>>::new();
    let frame = b.base + b.parts.len();
    for (index, (descriptor, members)) in domains.iter().enumerate() {
        c.checkpoint(Checkpoint::RationalPolyhedron)?;
        let alternatives = known
            .entry((descriptor.occurrence, members.len()))
            .or_default();
        let mut previous = None;
        for (elements, domain) in alternatives.iter() {
            c.checkpoint(Checkpoint::RationalPolyhedron)?;
            if *elements == members {
                previous = Some(*domain);
                break;
            }
        }
        let domain = if let Some(domain) = previous {
            domain
        } else {
            let mut elements = Vec::new();
            for member in members {
                elements.push(b.captured_scalar(member, requirements, c)?);
            }
            let domain = b.push(
                NodeType::Domain,
                "domain",
                Json::obj([
                    ("kind", Json::str("finite")),
                    ("type", descriptor.ty.wire()),
                    (
                        "elements",
                        Json::Arr(elements.iter().map(|element| element.wire()).collect()),
                    ),
                ]),
                requirements.iter().chain(&elements).copied().collect(),
                None,
            )?;
            b.parts[domain.0 - b.base].domain_type = Some(descriptor.ty.clone());
            alternatives.push((members, domain));
            domain
        };
        let context = crate::observed::call::Context {
            request: b.base,
            frame: Some(frame),
            iteration: Some(index),
            ..descriptor.context.unwrap_or_default()
        };
        quantifiers.push(Quantifier {
            domain: Some(domain),
            context: Some(context),
            ..descriptor.clone()
        });
    }
    Ok(quantifiers)
}

pub(super) fn build(
    b: &mut Builder<'_>,
    linear: &Linear,
    requirements: &[NodeRef],
    partial_architecture: bool,
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
    )?;
    let quantifiers = materialize_quantifiers(b, &linear.quantifiers, requirements, c)?;
    let equations = map(b, pm, em, &linear.equations, n, c)?;
    let part = &mut b.parts[equations.0 - b.base];
    if partial_architecture {
        part.support.make_owned().extend(
            linear
                .constraint_support
                .iter()
                .filter(|fact| fact.field.is_none() || fact.atom.is_some())
                .cloned(),
        );
    }
    for quantifier in quantifiers {
        part.arguments.extend(quantifier.domain);
        part.scope.add_quantifier(quantifier);
    }
    part.scope.merge(&linear.scope);
    part.arguments.sort_by_key(|node| node.0);
    part.arguments.dedup();
    let rhs = vector(b, em, &linear.rhs, c)?;
    let partial_obstruction = if partial_architecture
        && let Solutions::Affine(fiber) = &linear.solutions
        && let Some(index) = fiber.obstruction
    {
        use crate::observed::{environment::field_change::Polyhedron, field_polyhedron};
        let rows = field_polyhedron::halfspaces(&linear.equations, &linear.rhs, &[], c)?;
        let outcome = field_polyhedron::affine_obstruction(
            &fiber.left[index],
            &fiber.transformed_rhs[index],
            n,
            c,
        )?;
        field_polyhedron::verify(&rows, n, &outcome, c)?;
        Some(Solutions::Polyhedron(Polyhedron {
            inequalities: vec![],
            outcome,
        }))
    } else {
        None
    };
    let fiber = match partial_obstruction.as_ref().unwrap_or(&linear.solutions) {
        Solutions::Affine(fiber) => fiber,
        Solutions::Polyhedron(polyhedron) => {
            return super::field_polyhedron_result::build(
                b,
                linear,
                polyhedron,
                ring,
                pm,
                parameters,
                states,
                action,
                equations,
                rhs,
                requirements,
                c,
            );
        }
    };
    let mut args = vec![equations, rhs];
    args.extend(requirements);
    let (certificate, representation, representation_args) = if let Some(p) = &fiber.particular {
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
            return Err(internal!("有理全解の特解が元の線形系を満たさない").into());
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
        )?;
        let rank = n - fiber.pivots.len();
        let directions = module(b, ring, rank, "kernel", vec![equations])?;
        let embedding = map(b, directions, pm, &fiber.kernel, rank, c)?;
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
        let row = fiber
            .obstruction
            .ok_or(internal!("有理不整合の左零化子がない"))?;
        let coefficients = &fiber.left[row];
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
                return Err(internal!("有理空解の左零化子が元行列を零化しない").into());
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
        if paired == zero || paired != fiber.transformed_rhs[row] {
            return Err(internal!("有理空解の左零化子と元右辺の非零積が不一致").into());
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
