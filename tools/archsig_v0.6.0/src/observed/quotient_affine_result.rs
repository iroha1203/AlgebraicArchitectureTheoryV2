//! 整数Viewの実アフィン像。終域を周囲の格子全体に置き換えない。
use super::*;
use crate::observed::{
    change_result::{CandidateInput, linear_result as linear},
    environment::quotient_affine,
    integer_fiber,
};
use num_bigint::BigInt as Z;
use num_traits::Zero;

pub(super) fn compute(
    env: &Environment<'_>,
    g: &Graph,
    input: CandidateInput,
    reference: NodeRef,
    request: &Request,
    base: usize,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    let image = quotient_affine::compute(env, g, &input, request, c)?;
    let declaration =
        &env.inputs.law().declarations[request.declaration().ok_or("整数商のViewがない")?];
    let Signature::View { body, .. } = &declaration.signature else {
        return Err("整数商のView署名が違う".into());
    };
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let bindings = image
        .bindings
        .iter()
        .map(|(name, value)| {
            let selector = &request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{name}"))
                .ok_or("整数商の束縛がない")?
                .value;
            let r = if matches!(selector, Selector::Answer { .. }) {
                match env.answer_binding(g, selector, (0, 0))? {
                    AnswerBinding::Reference(r) => r,
                    AnswerBinding::Projection(node) => g
                        .nodes
                        .iter()
                        .position(|n| *n == node)
                        .map(NodeRef)
                        .ok_or("整数商の公開束縛が保持されていない")?,
                    AnswerBinding::Inapplicable(_) => {
                        return Err(ValidationFailure::from("整数商の束縛射影が不適合"));
                    }
                }
            } else {
                change_result::value(&mut b, value)?
            };
            Ok((name.clone(), r))
        })
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    let expression = change_result::source_expression(&mut b, env, *body, &bindings, &[])?;
    let part = &mut b.parts[expression.0 - base];
    part.arguments.push(reference);
    part.arguments.sort_by_key(|r| r.0);
    part.arguments.dedup();
    part.scope.merge(&g.get(reference)?.scope);
    part.scope.merge(&image.scope);
    part.scope.readings.insert(declaration.reading.clone());
    if !image.missing.is_empty() {
        let reason = Reason {
            kind: ReasonKind::Missing,
            request: request.id.clone(),
            dependencies: vec![expression],
            missing: image.missing,
            location: Some(Location::Law {
                span: declaration.span,
            }),
        };
        b.parts[expression.0 - base].reasons.push(reason.clone());
        let scope = b.parts[expression.0 - base].scope.clone();
        return Ok(Source {
            base,
            parts: b.parts,
            answer: Answer {
                id: request.id.clone(),
                status: Decision::Undetermined,
                outputs: BTreeMap::new(),
                claim: None,
                evidence: vec![],
                reasons: vec![reason],
                scope,
            },
            request: request.clone(),
            witness: input.witness,
            domain_type: input.domain_type,
        });
    }
    let source = b.push(
        NodeType::Domain,
        "domain",
        match &input.domain_type {
            ProjectionType::CandidateSpace(_) => Json::obj([
                ("kind", Json::str("candidates")),
                ("space", reference.wire()),
            ]),
            ProjectionType::SolutionSet(_) => Json::obj([
                ("kind", Json::str("solutions")),
                ("solutions", reference.wire()),
            ]),
            _ => return Err("整数商の元domain型が違う".into()),
        },
        vec![reference, expression],
        None,
        None,
    )?;
    let (classes, projection, representation) = if image.empty {
        let parameter_type = Type::Tuple(vec![
            Type::Z;
            input
                .search
                .linear
                .as_ref()
                .ok_or("整数商の元parameterがない")?
                .parameter_count
        ]);
        let classes = domain(
            &mut b,
            &Type::Set(Box::new(parameter_type)),
            &[],
            &[reference, expression],
        )?;
        let projection = b.push(
            NodeType::Construction(T::StateMap),
            "state_map",
            Json::obj([
                ("source", source.wire()),
                ("target", classes.wire()),
                ("kind", Json::str("finite")),
                ("pairs", Json::Arr(vec![])),
            ]),
            vec![source, classes],
            None,
            None,
        )?;
        (
            classes,
            projection,
            Json::obj([("kind", Json::str("finite")), ("fibers", Json::Arr(vec![]))]),
        )
    } else {
        let n = image.dimensions;
        let ring = b.push(
            NodeType::Construction(T::Ring),
            "ring",
            Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str("Z"))]),
            vec![],
            None,
            None,
        )?;
        let original = linear::module(&mut b, ring, image.origin.len(), "free", vec![reference])?;
        let parameters = linear::module(&mut b, ring, n, "free", vec![reference])?;
        // 元Assignmentへの復元は、解集合またはguardで選んだ同じ表示を使う。
        let embedding = linear::map(&mut b, parameters, original, &image.embedding, n, c)?;
        let origin = linear::vector(&mut b, original, &image.origin, c)?;
        let ambient = linear::module(&mut b, ring, 1, "free", vec![expression])?;
        let map = linear::map(&mut b, parameters, ambient, &image.matrix, n, c)?;
        let offset = linear::vector(&mut b, ambient, &image.offset, c)?;
        let fiber = integer_fiber::solve(&image.matrix, n, &[Z::zero()], c)?;
        let actual_image = linear::module(&mut b, ring, fiber.rank, "image", vec![map])?;
        let kernel = linear::module(&mut b, ring, n - fiber.rank, "kernel", vec![map])?;
        let basis = integer_fiber::multiply(&image.matrix, &fiber.right, n, c)?;
        let image_generators = (0..fiber.rank)
            .map(|j| {
                Json::obj([
                    ("type", Type::Z.wire()),
                    ("value", Scalar::Z(basis[0][j].clone()).wire()),
                ])
            })
            .collect();
        let kernel_generators = (0..n - fiber.rank)
            .map(|j| {
                let value = Scalar::Tuple(
                    fiber
                        .kernel
                        .iter()
                        .map(|row| Scalar::Z(row[j].clone()))
                        .collect(),
                );
                Json::obj([("type", value.ty().wire()), ("value", value.wire())])
            })
            .collect();
        for (r, generators) in [
            (actual_image, image_generators),
            (kernel, kernel_generators),
        ] {
            let Json::Obj(wire) = &mut b.parts[r.0 - base].wire else {
                return Err("整数商の加群がrecordでない".into());
            };
            wire.insert("generators".into(), Json::Arr(generators));
        }
        let inclusion = linear::map(&mut b, kernel, parameters, &fiber.kernel, n - fiber.rank, c)?;
        let image_basis = basis.iter().map(|row| row[..fiber.rank].to_vec()).collect();
        let image_inclusion =
            linear::map(&mut b, actual_image, ambient, &image_basis, fiber.rank, c)?;
        let ambient_domain = linear::domain(&mut b, ambient)?;
        let view = b.push(
            NodeType::Construction(T::StateMap),
            "state_map",
            Json::obj([
                ("source", source.wire()),
                ("target", ambient_domain.wire()),
                ("kind", Json::str("affine")),
                ("linear", map.wire()),
                ("offset", offset.wire()),
            ]),
            vec![source, ambient_domain, map, offset, embedding, origin],
            None,
            None,
        )?;
        let classes = b.push(
            NodeType::Domain,
            "domain",
            Json::obj([
                ("kind", Json::str("image")),
                ("map", view.wire()),
                ("source", reference.wire()),
            ]),
            vec![view, reference],
            None,
            None,
        )?;
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
            vec![
                source,
                classes,
                map,
                offset,
                embedding,
                origin,
                inclusion,
                image_inclusion,
            ],
            None,
            None,
        )?;
        (
            classes,
            projection,
            Json::obj([
                ("kind", Json::str("affine")),
                ("image", actual_image.wire()),
                ("kernel", kernel.wire()),
                ("map", map.wire()),
                ("offset", offset.wire()),
            ]),
        )
    };
    let mut args = (base..base + b.parts.len())
        .map(NodeRef)
        .collect::<Vec<_>>();
    args.push(reference);
    let quotient = b.push(
        NodeType::Construction(T::Quotient),
        "quotient",
        Json::obj([
            ("domain", reference.wire()),
            (
                "view",
                Json::str(request.declaration().ok_or("整数商のViewがない")?),
            ),
            (
                "bindings",
                Json::Arr(
                    bindings
                        .iter()
                        .map(|(name, value)| {
                            Json::obj([("name", Json::str(name)), ("value", value.wire())])
                        })
                        .collect(),
                ),
            ),
            ("classes", classes.wire()),
            ("projection", projection.wire()),
            ("representation", representation),
            ("evaluations", Json::Arr(vec![])),
        ]),
        args,
        None,
        None,
    )?;
    let scope = b.parts[quotient.0 - base].scope.clone();
    Ok(Source {
        base,
        parts: b.parts,
        answer: Answer {
            id: request.id.clone(),
            status: Decision::Established,
            outputs: BTreeMap::from([("quotient".into(), quotient)]),
            claim: None,
            evidence: vec![],
            reasons: vec![],
            scope,
        },
        request: request.clone(),
        witness: input.witness,
        domain_type: input.domain_type,
    })
}
