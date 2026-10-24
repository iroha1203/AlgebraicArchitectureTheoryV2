//! 元の整数候補座標上でViewを評価し、選択された部分域へ制限する。
use super::*;
use crate::law::model::Signature;
use crate::observed::{
    affine,
    change_result::CandidateInput,
    integer_fiber::{self, Matrix},
    object_evaluate::ObjectDomain,
    projection::ProjectionType,
};
use num_bigint::BigInt as Z;
use num_traits::{One, Zero};
use std::sync::Arc;

pub(in crate::observed) struct Law {
    pub name: String,
    pub bindings: Vec<(String, Scalar)>,
    pub operands: [usize; 2],
    pub matrix: Matrix,
    pub offset: Vec<Z>,
}
pub(in crate::observed) struct Image {
    pub law: Option<Law>,
    pub bindings: Vec<(String, Scalar)>,
    pub matrix: Matrix,
    pub offset: Vec<Z>,
    pub embedding: Matrix,
    pub origin: Vec<Z>,
    pub dimensions: usize,
    pub empty: bool,
    pub missing: Vec<Fact>,
    pub scope: Scope,
}
fn unsupported(request: &Request, feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law { span: (0, 0) },
        feature: format!("{}: {feature}", request.id),
    }
}
pub(in crate::observed) fn compute(
    original: &Environment<'_>,
    graph: &Graph,
    input: &CandidateInput,
    request: &Request,
    c: &mut Control,
) -> Result<Image, ValidationFailure> {
    c.checkpoint(Checkpoint::Quotient)?;
    if !input.search.complete {
        return Err(unsupported(request, "整数商の候補全域が未確定"));
    }
    let linear = input
        .search
        .linear
        .as_ref()
        .ok_or("整数商の線形表示がない")?;
    let decl =
        &original.inputs.law().declarations[request.declaration().ok_or("整数商のViewがない")?];
    let Signature::View {
        params,
        returns,
        body,
    } = &decl.signature
    else {
        return Err("整数商のheadがViewでない".into());
    };
    if *returns != Type::Z {
        return Err(unsupported(request, "整数商のこのView値型は未実装"));
    }
    let bindings = params
        .iter()
        .map(|p| {
            let arg = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
                .ok_or("整数商の束縛がない")?;
            Ok((
                p.name.clone(),
                change_search::selector(original, graph, &arg.value)?,
            ))
        })
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    let law = request
        .arguments
        .iter()
        .find(|a| a.name == "law")
        .map(|argument| {
            let Selector::Declaration { name } = &argument.value else {
                return Err(ValidationFailure::from("整数商のLaw名がない"));
            };
            let Signature::Law {
                params,
                body,
                guard,
                ..
            } = &original.inputs.law().declarations[name].signature
            else {
                return Err(ValidationFailure::from("整数商のLaw署名が違う"));
            };
            if guard.is_some() {
                return Err(unsupported(request, "整数商のguard付きLaw降下は未実装"));
            }
            let ExprKind::Binary {
                op: BinOp::Eq,
                lhs,
                rhs,
            } = original.inputs.law().exprs[*body].kind
            else {
                return Err(unsupported(
                    request,
                    "整数商の直下等式以外のLaw降下は未実装",
                ));
            };
            if original.inputs.law().expr_type(lhs) != Some(&Type::Z) {
                return Err(unsupported(request, "整数商のZ以外のLaw値型は未実装"));
            }
            let bindings = params
                .iter()
                .map(|p| {
                    let argument = request
                        .arguments
                        .iter()
                        .find(|a| a.name == format!("bind.{}", p.name))
                        .ok_or_else(|| {
                            unsupported(request, "整数商の未束縛Law parameterは未実装")
                        })?;
                    Ok((
                        p.name.clone(),
                        change_search::selector(original, graph, &argument.value)?,
                    ))
                })
                .collect::<Result<Vec<_>, ValidationFailure>>()?;
            Ok(Law {
                name: name.clone(),
                bindings,
                operands: [lhs, rhs],
                matrix: vec![],
                offset: vec![],
            })
        })
        .transpose()?;
    let n = linear.parameter_count;
    let (origin, embedding, dimensions, empty) =
        if matches!(input.domain_type, ProjectionType::SolutionSet(_)) {
            let dimensions = linear.kernel.first().map_or(0, Vec::len);
            (
                linear
                    .particular
                    .clone()
                    .unwrap_or_else(|| vec![Z::zero(); n]),
                linear.kernel.clone(),
                dimensions,
                linear.particular.is_none(),
            )
        } else if linear.candidates_empty {
            (vec![Z::zero(); n], vec![vec![]; n], 0, true)
        } else if let Some(guard) = &linear.guard {
            (
                guard
                    .fiber
                    .particular
                    .clone()
                    .ok_or("整数候補guardの原点がない")?,
                guard.fiber.kernel.clone(),
                n - guard.fiber.rank,
                false,
            )
        } else {
            let mut identity = vec![];
            for i in 0..n {
                c.checkpoint(Checkpoint::Quotient)?;
                let mut row = vec![Z::zero(); n];
                row[i] = Z::one();
                identity.push(row);
            }
            (vec![Z::zero(); n], identity, n, false)
        };
    let mut result = Image {
        law,
        bindings,
        matrix: vec![],
        offset: vec![],
        embedding,
        origin,
        dimensions,
        empty,
        missing: vec![],
        scope: Scope::default(),
    };
    if let Some(law) = &result.law {
        for binding in &law.bindings {
            if !result.bindings.iter().any(|(name, _)| name == &binding.0) {
                result.bindings.push(binding.clone());
            }
        }
    }
    if empty {
        return Ok(result);
    }
    let mut env = Environment::with_primitive_valuation(original.inputs, &input.assignments, c)?;
    env.object = Some(Arc::new(ObjectDomain::from_readings(
        original.inputs,
        input.witness.readings(),
        0,
        c,
    )?));
    env.missing_slot_reads.replace(Some(BTreeSet::new()));
    for ((slot, row), offset) in linear.slots.iter().zip(&linear.action).zip(&linear.offset) {
        let mut form =
            affine::constant(&Scalar::Z(offset.clone()), c)?.ok_or("整数商の定数がない")?;
        for (axis, coefficient) in linear.axes.iter().zip(row) {
            let parameter = affine::parameter(&Type::Z, axis, c)?;
            let coefficient = affine::constant(&Scalar::Z(coefficient.clone()), c)?;
            let term = affine::binary(BinOp::Mul, parameter.as_ref(), coefficient.as_ref(), c)?;
            form = affine::binary(BinOp::Add, Some(&form), term.as_ref(), c)?
                .ok_or("整数商の更新式がない")?;
        }
        env.affine_valuation.insert(slot.clone(), form);
    }
    let mut vars = BTreeMap::new();
    let mut checked = BTreeMap::new();
    let mut checks = owned_call::Checks::default();
    for (param, (name, v)) in params.iter().zip(&result.bindings) {
        env.owned_call_value_check(
            &param.ty,
            &crate::observed::term::affine::Value::Known(v.clone()),
            &checked,
            &decl.reading,
            decl.span,
            &mut checks,
        )?;
        checked.insert(name.as_str(), Some(v));
        vars.insert(
            name.clone(),
            SourceValue {
                known_value: Some(v.clone()),
                scalar_scope: Some(Scope::default()),
                scope: Scope::default(),
                support: vec![],
                condition_failed: false,
                condition_pending: false,
                symbolic: None,
                comparison: None,
                affine: affine::constant(v, c)?.map(Box::new),
            },
        );
    }
    result.scope.merge(&checks.scope);
    if checks.failure.is_some() || checks.blocked {
        result.missing = checks.missing;
        if !result.missing.is_empty() {
            return Ok(result);
        }
        return Err(unsupported(
            request,
            "整数商のView適用条件の公開配送は未実装",
        ));
    }
    let value = env.scoped_ast(*body, &vars, &Scope::default(), &decl.reading)?;
    result.scope.merge(&value.scope);
    result.missing = env
        .missing_slot_reads
        .take()
        .ok_or("整数商の不足収集がない")?
        .into_iter()
        .collect();
    if value.condition_failed || value.condition_pending {
        if !result.missing.is_empty() {
            return Ok(result);
        }
        return Err(unsupported(request, "整数商のView構成条件が未成立"));
    }
    let coordinates = value
        .affine
        .as_ref()
        .map(|form| form.integer_coordinates(&linear.axes, c))
        .transpose()?
        .flatten();
    let Some((constant, row)) = coordinates else {
        if !result.missing.is_empty() {
            return Ok(result);
        }
        return Err(unsupported(
            request,
            "整数商のViewが候補parameterのZアフィン式でない",
        ));
    };
    result.missing.clear();
    let mut offset = constant;
    for (a, x) in row.iter().zip(&result.origin) {
        c.checkpoint(Checkpoint::Quotient)?;
        offset += a * x;
    }
    result.matrix = integer_fiber::multiply(&vec![row], &result.embedding, dimensions, c)?;
    result.offset = vec![offset];
    if let Some(law) = &mut result.law {
        let declaration = &original.inputs.law().declarations[&law.name];
        let Signature::Law { params, .. } = &declaration.signature else {
            return Err("整数商のLaw署名がない".into());
        };
        let mut vars = BTreeMap::new();
        let mut checked = BTreeMap::new();
        let mut checks = owned_call::Checks::default();
        for (param, (name, v)) in params.iter().zip(&law.bindings) {
            env.owned_call_value_check(
                &param.ty,
                &crate::observed::term::affine::Value::Known(v.clone()),
                &checked,
                &declaration.reading,
                declaration.span,
                &mut checks,
            )?;
            checked.insert(name.as_str(), Some(v));
            vars.insert(
                name.clone(),
                SourceValue {
                    known_value: Some(v.clone()),
                    scalar_scope: Some(Scope::default()),
                    scope: Scope::default(),
                    support: vec![],
                    condition_failed: false,
                    condition_pending: false,
                    symbolic: None,
                    comparison: None,
                    affine: affine::constant(v, c)?.map(Box::new),
                },
            );
        }
        result.scope.merge(&checks.scope);
        if checks.failure.is_some() || checks.blocked {
            result.missing = checks.missing;
            if !result.missing.is_empty() {
                return Ok(result);
            }
            return Err(unsupported(
                request,
                "整数商のLaw適用条件の公開配送は未実装",
            ));
        }
        result.scope.readings.insert(declaration.reading.clone());
        for operand in law.operands {
            env.missing_slot_reads.replace(Some(BTreeSet::new()));
            let value = env.scoped_ast(operand, &vars, &Scope::default(), &declaration.reading)?;
            result.scope.merge(&value.scope);
            let missing = env
                .missing_slot_reads
                .take()
                .ok_or("整数Law商の不足収集がない")?;
            let coordinates = value
                .affine
                .as_ref()
                .map(|f| f.integer_coordinates(&linear.axes, c))
                .transpose()?
                .flatten();
            if value.condition_failed || value.condition_pending || coordinates.is_none() {
                result.missing.extend(missing);
                if !result.missing.is_empty() {
                    return Ok(result);
                }
                return Err(unsupported(
                    request,
                    "整数商のLaw値が確定したZアフィン式でない",
                ));
            }
            let (mut constant, row) = coordinates.ok_or("整数Law商の係数がない")?;
            for (a, x) in row.iter().zip(&result.origin) {
                c.checkpoint(Checkpoint::Quotient)?;
                constant += a * x;
            }
            law.matrix.extend(integer_fiber::multiply(
                &vec![row],
                &result.embedding,
                dimensions,
                c,
            )?);
            law.offset.push(constant);
        }
    }
    Ok(result)
}

/// 核の反例を元Assignmentへ戻し、同じ通常評価器で左右の実値を確認する。
pub(in crate::observed) fn point(
    original: &Environment<'_>,
    input: &CandidateInput,
    image: &Image,
    coordinates: &[Z],
    request: &Request,
    c: &mut Control,
) -> Result<quotient_evaluation::Row, ValidationFailure> {
    let law = image.law.as_ref().ok_or("整数商のLawがない")?;
    let linear = input.search.linear.as_ref().ok_or("整数商の更新式がない")?;
    let apply = |matrix: &Matrix, offset: &[Z], point: &[Z]| -> Result<Vec<Z>, ValidationFailure> {
        matrix
            .iter()
            .zip(offset)
            .map(|(row, constant)| {
                if row.len() != point.len() {
                    return Err("整数商の点の次元が違う".into());
                }
                let mut value = constant.clone();
                for (a, x) in row.iter().zip(point) {
                    original.tick()?;
                    value += a * x;
                }
                Ok(value)
            })
            .collect()
    };
    let parameters = apply(&image.embedding, &image.origin, coordinates)?;
    let values = apply(&linear.action, &linear.offset, &parameters)?;
    let mut assignments = input
        .assignments
        .iter()
        .cloned()
        .collect::<BTreeMap<_, _>>();
    assignments.extend(
        linear
            .slots
            .iter()
            .cloned()
            .zip(values.into_iter().map(Scalar::Z)),
    );
    let assignments = assignments.into_iter().collect::<Vec<_>>();
    let mut env = Environment::with_primitive_valuation(original.inputs, &assignments, c)?;
    env.object = Some(Arc::new(ObjectDomain::from_readings(
        original.inputs,
        input.witness.readings(),
        0,
        c,
    )?));
    let declaration = &original.inputs.law().declarations[&law.name];
    let Signature::Law { body, .. } = &declaration.signature else {
        return Err("整数商のLaw署名がない".into());
    };
    env.evaluation_capture
        .replace(Some(quotient_evaluation::EvaluationCapture {
            selected: vec![*body],
            nodes: vec![],
            roots: vec![],
            stack: vec![],
        }));
    let evaluated = finite_law_valuations::evaluate_point(&env, declaration, &law.bindings, 0);
    let capture = env
        .evaluation_capture
        .take()
        .ok_or("整数商のLaw評価出現がない")?;
    let evaluated = evaluated?;
    if evaluated.application != Some(true)
        || evaluated.guard != Some(true)
        || evaluated.condition_failed
        || evaluated.condition_pending
    {
        return Err(unsupported(request, "整数商の反例点でLaw評価が未確定"));
    }
    let Some((_, Some(left), Some(right))) = evaluated.operands else {
        return Err("整数商の反例の左右値がない".into());
    };
    let expected = apply(&law.matrix, &law.offset, coordinates)?;
    if vec![left.clone(), right.clone()] != expected.into_iter().map(Scalar::Z).collect::<Vec<_>>()
    {
        return Err("整数商の正規形と通常Law評価が違う".into());
    }
    let declaration =
        &original.inputs.law().declarations[request.declaration().ok_or("整数商のViewがない")?];
    let Signature::View {
        body: view_body, ..
    } = &declaration.signature
    else {
        return Err("整数商のView署名がない".into());
    };
    let vars = image
        .bindings
        .iter()
        .map(|(name, v)| {
            (
                name.clone(),
                SourceValue {
                    known_value: Some(v.clone()),
                    scalar_scope: Some(Scope::default()),
                    scope: Scope::default(),
                    support: vec![],
                    condition_failed: false,
                    condition_pending: false,
                    symbolic: None,
                    comparison: None,
                    affine: None,
                },
            )
        })
        .collect();
    let view = env.scoped_ast(*view_body, &vars, &Scope::default(), &declaration.reading)?;
    let expected = apply(&image.matrix, &image.offset, coordinates)?;
    let view = view.known_value.ok_or("整数商の反例のView値がない")?;
    if expected.len() != 1 || view != Scalar::Z(expected[0].clone()) {
        return Err("整数商の正規形と通常View評価が違う".into());
    }
    let body_evaluation = capture
        .roots
        .iter()
        .copied()
        .find(|i| capture.nodes[*i].expression == *body);
    Ok(quotient_evaluation::Row {
        parameters: Scalar::Tuple(parameters.into_iter().map(Scalar::Z).collect()),
        image: view,
        assignments,
        laws: vec![quotient_evaluation::LawRow {
            evaluations: capture.nodes,
            body_evaluation,
            guard_evaluation: None,
            bindings: law.bindings.clone(),
            guard: true,
            values: Some((left, right)),
            scope: evaluated.scope,
        }],
    })
}
