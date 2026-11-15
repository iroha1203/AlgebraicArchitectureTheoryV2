//! Q 多面体上のアフィン View の像と、元 parameter 座標上の指定ファイバー。
use super::*;
use crate::observed::{
    change_result::{CandidateInput, field_linear_result, linear_result},
    environment::quotient_affine::{Image, verify_polyhedral_points},
    field_polyhedron::{self, Halfspace, Outcome},
    numeric,
};
use archsig_common::control::Checkpoint;
use archsig_input::law::ast::{BinOp, UnOp};

pub(super) struct ResultParts {
    pub classes: NodeRef,
    pub projection: NodeRef,
    pub fiber: Option<NodeRef>,
    pub representation: Json,
}

fn vector(values: &[Scalar]) -> Json {
    Json::Arr(values.iter().map(Scalar::wire).collect())
}

fn constraints(rows: &[Halfspace], c: &Control) -> Result<Json, ValidationFailure> {
    Ok(Json::Arr(
        rows.iter()
            .map(|row| {
                c.checkpoint(Checkpoint::Quotient)?;
                Ok(Json::obj([
                    ("coefficients", vector(&row.coefficients)),
                    ("upper", row.rhs.wire()),
                ]))
            })
            .collect::<Result<_, ValidationFailure>>()?,
    ))
}

fn flatten(
    value: &Scalar,
    coordinates: &mut Vec<Scalar>,
    c: &Control,
) -> Result<(), ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        c.checkpoint(Checkpoint::Quotient)?;
        match value {
            Scalar::Tuple(items) => {
                for item in items {
                    flatten(item, coordinates, c)?;
                }
            }
            Scalar::Q(..) => coordinates.push(value.clone()),
            _ => return Err(internal!("多面体のView値にQ以外が含まれる").into()),
        }
        Ok(())
    })
}

pub(super) fn build(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    input: &CandidateInput,
    image: &Image,
    ([solutions, expression, source], at): ([NodeRef; 3], Option<NodeRef>),
    request: &Request,
    c: &Control,
) -> Result<ResultParts, ValidationFailure> {
    let (linear, polyhedron) = input
        .rational_polyhedron()
        .ok_or(internal!("元の有理多面体がない"))?;
    let n = linear.parameter_count;
    let m = image.matrix.len();
    let zero = numeric::zero(&Type::Q, c)?;
    let negative_one = numeric::unary(UnOp::Neg, &numeric::literal("1", &Type::Q, c)?, c)?;
    let empty = matches!(polyhedron.outcome, Outcome::Empty(_));
    let mut original = if empty && at.is_none() {
        vec![]
    } else {
        field_polyhedron::halfspaces(&linear.equations, &linear.rhs, &polyhedron.inequalities, c)?
    };
    let projected = if empty {
        vec![Halfspace {
            coefficients: vec![zero.clone(); m],
            rhs: negative_one.clone(),
        }]
    } else {
        // Mx + b = y を付け、x だけを消去する。返す行の座標は View の成分順。
        let mut graph = if at.is_some() {
            original.clone()
        } else {
            std::mem::take(&mut original)
        };
        for row in &mut graph {
            c.checkpoint(Checkpoint::Quotient)?;
            row.coefficients.resize(n + m, zero.clone());
        }
        let mut equations = Vec::with_capacity(m);
        for (i, row) in image.matrix.iter().enumerate() {
            c.checkpoint(Checkpoint::Quotient)?;
            let mut equation = row.clone();
            equation.resize(n + m, zero.clone());
            equation[n + i] = negative_one.clone();
            equations.push(equation);
        }
        let rhs = image
            .offset
            .iter()
            .map(|offset| numeric::binary(BinOp::Sub, &zero, offset, c))
            .collect::<Result<Vec<_>, _>>()?;
        graph.extend(field_polyhedron::halfspaces(&equations, &rhs, &[], c)?);
        field_polyhedron::project_trailing(graph, n, m, c)?
    };
    let classes = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("rational_polyhedron")),
            ("type", image.view_type.wire()),
            ("halfspaces", constraints(&projected, c)?),
        ]),
        vec![solutions, expression],
        None,
    )?;
    let ring = b.push(
        NodeType::Construction(T::Ring),
        "ring",
        Json::obj([("kind", Json::str("scalar")), ("scalar", Type::Q.wire())]),
        vec![],
        None,
    )?;
    let parameters = linear_result::module(b, ring, n, "free", vec![solutions])?;
    let ambient = linear_result::module(b, ring, m, "free", vec![expression])?;
    let map = field_linear_result::map(b, parameters, ambient, &image.matrix, n, c)?;
    let offset = field_linear_result::vector(b, ambient, &image.offset, c)?;
    let projection = b.push(
        NodeType::Construction(T::StateMap),
        "state_map",
        Json::obj([
            ("source", source.wire()),
            ("target", classes.wire()),
            ("kind", Json::str("affine")),
            ("linear", map.wire()),
            ("offset", offset.wire()),
        ]),
        vec![source, classes, map, offset],
        None,
    )?;
    let fiber = if let Some(at) = at {
        let value = b.g.scalar(at)?;
        let mut coords = Vec::new();
        flatten(value, &mut coords, c)?;
        if coords.len() != m || value.ty() != image.view_type {
            return Err(internal!("多面体のファイバー指定が View 型と違う").into());
        }
        let rhs = coords
            .iter()
            .zip(&image.offset)
            .map(|(coordinate, offset)| numeric::binary(BinOp::Sub, coordinate, offset, c))
            .collect::<Result<Vec<_>, _>>()?;
        original.extend(field_polyhedron::halfspaces(&image.matrix, &rhs, &[], c)?);
        let result = field_polyhedron::solve(&original, n, c)?;
        field_polyhedron::verify(&original, n, &result, c)?;
        let points: &[&[Scalar]] = match &result {
            Outcome::Empty(_) => &[],
            Outcome::Unique { point, .. } => &[point],
            Outcome::Multiple { first, second } => &[first, second],
        };
        verify_polyhedral_points(env, input, image, points, value, request, c)?;
        let (kind, witnesses) = match result {
            Outcome::Empty(row) => (
                "empty",
                vec![("contradiction".into(), vector(&row.combination))],
            ),
            Outcome::Unique { point, bounds } => (
                "unique",
                vec![
                    ("point".into(), vector(&point)),
                    (
                        "coordinate_bounds".into(),
                        Json::Arr(
                            bounds
                                .iter()
                                .map(|(lo, hi)| {
                                    Json::obj([
                                        ("lower", vector(&lo.combination)),
                                        ("upper", vector(&hi.combination)),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                ],
            ),
            Outcome::Multiple { first, second } => (
                "multiple",
                vec![
                    ("point".into(), vector(&first)),
                    ("second".into(), vector(&second)),
                ],
            ),
        };
        let mut wire = archsig_common::canonical::JsonObject::from([
            ("kind".into(), Json::str("rational_polyhedron")),
            ("type".into(), Type::Tuple(vec![Type::Q; n]).wire()),
            ("halfspaces".into(), constraints(&original, c)?),
            ("outcome".into(), Json::str(kind)),
            ("solutions".into(), solutions.wire()),
        ]);
        for (name, value) in witnesses {
            wire.insert(name, value);
        }
        wire.insert("at".into(), at.wire());
        Some(b.push(
            NodeType::Domain,
            "domain",
            Json::Obj(wire),
            vec![solutions, projection, at],
            None,
        )?)
    } else {
        None
    };
    let representation = Json::obj([
        ("kind", Json::str("rational_polyhedron")),
        ("view_type", image.view_type.wire()),
        ("linear", map.wire()),
        ("offset", offset.wire()),
    ]);
    Ok(ResultParts {
        classes,
        projection,
        fiber,
        representation,
    })
}
