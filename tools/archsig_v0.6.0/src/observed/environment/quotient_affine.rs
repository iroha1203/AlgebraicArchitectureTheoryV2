//! 元のZ/Q候補座標上でViewを評価し、選択された部分域へ制限する。
use super::*;
use crate::law::model::Signature;
use crate::observed::{
    affine, change_result::CandidateInput, field_fiber::Matrix, numeric,
    object_evaluate::ObjectDomain, projection::ProjectionType,
};
pub(in crate::observed) mod coefficients;
use std::sync::Arc;

pub(in crate::observed) enum Guard {
    Fixed(bool),
    Affine(change_affine::NumericGuard),
}
impl Guard {
    pub fn never(&self) -> bool {
        matches!(self, Self::Fixed(false))
    }
    fn at(
        &self,
        coordinates: &[Scalar],
        ty: &Type,
        c: &Control,
    ) -> Result<bool, ValidationFailure> {
        match self {
            Self::Fixed(value) => Ok(*value),
            Self::Affine(domain) => {
                for (row, rhs) in domain.equations.iter().zip(&domain.rhs) {
                    if row.len() != coordinates.len() {
                        return Err("商のguard座標の次元が違う".into());
                    }
                    let mut value = numeric::zero(ty, c)?;
                    for (a, x) in row.iter().zip(coordinates) {
                        value = coefficients::add_product(&value, a, x, c)?;
                    }
                    if value != *rhs {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
    }
}
pub(in crate::observed) struct Instance {
    pub bindings: Vec<(String, Scalar)>,
    pub guard: Guard,
    pub rows: std::ops::Range<usize>,
}
pub(in crate::observed) struct Law {
    pub name: String,
    pub instances: Vec<Instance>,
    pub bindings: Vec<(String, Scalar)>,
    pub operands: [usize; 2],
    pub pending_expression: Option<usize>,
    pub value_type: Type,
    pub matrix: Matrix,
    pub offset: Vec<Scalar>,
}
pub(in crate::observed) struct Image {
    pub ty: Type,
    pub view_type: Type,
    pub parameter_count: usize,
    pub law: Option<Law>,
    pub bindings: Vec<(String, Scalar)>,
    pub matrix: Matrix,
    pub offset: Vec<Scalar>,
    pub embedding: Matrix,
    pub origin: Vec<Scalar>,
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
        return Err(unsupported(request, "アフィン商の候補全域が未確定"));
    }
    let linear = coefficients::Input::from_search(&input.search, c)?;
    let ty = &linear.ty;
    let decl = &original.indexes.inputs.law().declarations()
        [request.declaration().ok_or("アフィン商のViewがない")?];
    let Signature::View {
        params,
        returns,
        body,
    } = &decl.signature
    else {
        return Err("アフィン商のheadがViewでない".into());
    };
    if !coefficients::view_type(returns, ty, c)? {
        return Err(unsupported(request, "アフィン商のこのView値型は未実装"));
    }
    let bindings = params
        .iter()
        .map(|p| {
            let arg = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
                .ok_or("アフィン商の束縛がない")?;
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
                return Err(ValidationFailure::from("アフィン商のLaw名がない"));
            };
            let Signature::Law { params, body, .. } =
                &original.indexes.inputs.law().declarations()[name].signature
            else {
                return Err(ValidationFailure::from("アフィン商のLaw署名が違う"));
            };
            let ExprKind::Binary {
                op: BinOp::Eq,
                lhs,
                rhs,
            } = original.indexes.inputs.law().exprs()[*body].kind
            else {
                return Err(unsupported(
                    request,
                    "アフィン商の直下等式以外のLaw降下は未実装",
                ));
            };
            let value_type = original
                .indexes
                .inputs
                .law()
                .expr_type(lhs)
                .ok_or("商のLaw値型がない")?;
            if !coefficients::view_type(value_type, ty, c)? {
                return Err(unsupported(
                    request,
                    "アフィン商の指定係数以外のLaw値型は未実装",
                ));
            }
            let mut bindings = vec![];
            for p in params {
                if let Some(argument) = request
                    .arguments
                    .iter()
                    .find(|a| a.name == format!("bind.{}", p.name))
                {
                    bindings.push((
                        p.name.clone(),
                        change_search::selector(original, graph, &argument.value)?,
                    ));
                }
            }
            Ok(Law {
                name: name.clone(),
                instances: vec![],
                bindings,
                operands: [lhs, rhs],
                pending_expression: None,
                value_type: value_type.clone(),
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
                    .unwrap_or(vec![numeric::zero(ty, c)?; n]),
                linear.kernel.clone(),
                dimensions,
                linear.particular.is_none(),
            )
        } else {
            (
                linear
                    .guard_origin
                    .clone()
                    .unwrap_or(vec![numeric::zero(ty, c)?; n]),
                linear.guard_kernel.clone(),
                linear.guard_dimensions,
                linear.guard_origin.is_none(),
            )
        };
    let mut result = Image {
        ty: ty.clone(),
        view_type: returns.clone(),
        parameter_count: n,
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
    let mut env =
        Environment::with_primitive_valuation(original.indexes.inputs, &input.assignments, c)?;
    env.indexes.object = Some(Arc::new(ObjectDomain::from_readings(
        original.indexes.inputs,
        input.witness.readings(),
        0,
        c,
    )?));
    env.state.missing_slot_reads.replace(Some(BTreeSet::new()));
    set_action(
        &mut env,
        &linear.slots,
        &linear.action,
        &linear.offset,
        &linear.axes,
        ty,
        c,
    )?;
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
            "アフィン商のView適用条件の公開配送は未実装",
        ));
    }
    let value = env.scoped_ast(*body, &vars, &Scope::default(), &decl.reading)?;
    result.scope.merge(&value.scope);
    result.missing = env
        .state
        .missing_slot_reads
        .take()
        .ok_or("アフィン商の不足収集がない")?
        .into_iter()
        .collect();
    if value.condition_failed || value.condition_pending {
        if !result.missing.is_empty() {
            return Ok(result);
        }
        return Err(unsupported(request, "アフィン商のView構成条件が未成立"));
    }
    let symbolic = env.symbolic_source(*body, &vars, &Scope::default(), &decl.reading)?;
    let coordinates = coefficients::view_coordinates(&symbolic, &linear.axes, ty, c)?;
    let Some((mut constants, rows)) = coordinates else {
        if !result.missing.is_empty() {
            return Ok(result);
        }
        return Err(unsupported(request, "商のViewが指定係数のアフィン式でない"));
    };
    result.missing.clear();
    for (constant, row) in constants.iter_mut().zip(&rows) {
        for (a, x) in row.iter().zip(&result.origin) {
            *constant = coefficients::add_product(constant, a, x, c)?;
        }
    }
    result.matrix = coefficients::multiply(ty, &rows, &result.embedding, dimensions, c)?;
    result.offset = constants;
    if let Some(law) = &mut result.law {
        let declaration = &original.indexes.inputs.law().declarations()[&law.name];
        let Signature::Law { params, guard, .. } = &declaration.signature else {
            return Err("商のLaw署名がない".into());
        };
        let mut instances = vec![vec![]];
        for p in params {
            let values = if let Some((_, v)) = law.bindings.iter().find(|(n, _)| n == &p.name) {
                vec![v.clone()]
            } else {
                result.scope.quantifiers.push(Quantifier {
                    kind: crate::law::ast::QuantKind::Forall,
                    name: p.name.clone(),
                    ty: p.ty.clone(),
                    domain: None,
                    occurrence: p.span,
                    context: None,
                });
                let values = change_search::domain(&env, &p.ty, p.span, &mut result.missing)?;
                let Some(values) = values else {
                    if !result.missing.is_empty() {
                        return Ok(result);
                    }
                    return Err(unsupported(request, "商のLaw parameter域が未確定"));
                };
                values
            };
            let mut next = vec![];
            for instance in instances {
                for value in &values {
                    c.checkpoint(Checkpoint::Quotient)?;
                    let mut row = instance.clone();
                    row.push((p.name.clone(), value.clone()));
                    next.push(row)
                }
            }
            instances = next;
        }
        // guard は選択した全アフィン域上で通常評価する。元parameterの一点には代入しない。
        let selected = if guard.is_some() {
            let mut selected = Environment::with_primitive_valuation(
                original.indexes.inputs,
                &input.assignments,
                c,
            )?;
            selected.indexes.object = env.indexes.object.clone();
            let matrix =
                coefficients::multiply(ty, &linear.action, &result.embedding, dimensions, c)?;
            let mut offset = linear.offset.clone();
            for (value, row) in offset.iter_mut().zip(&linear.action) {
                for (a, x) in row.iter().zip(&result.origin) {
                    *value = coefficients::add_product(value, a, x, c)?;
                }
            }
            set_action(
                &mut selected,
                &linear.slots,
                &matrix,
                &offset,
                &linear.axes[..dimensions],
                ty,
                c,
            )?;
            Some(selected)
        } else {
            None
        };
        result.scope.readings.insert(declaration.reading.clone());
        for bindings in instances {
            let mut vars = BTreeMap::new();
            let mut checked = BTreeMap::new();
            let mut checks = owned_call::Checks::default();
            for (param, (name, v)) in params.iter().zip(&bindings) {
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
            if checks.failure.is_some() {
                continue;
            }
            if checks.blocked {
                result.missing.extend(checks.missing);
                if !result.missing.is_empty() {
                    return Ok(result);
                }
                return Err(unsupported(request, "商のLaw適用条件が未確定"));
            }
            let applies = if let Some(guard) = guard {
                let selected = selected.as_ref().ok_or("商のguard評価域がない")?;
                selected
                    .state
                    .missing_slot_reads
                    .replace(Some(BTreeSet::new()));
                let value =
                    selected.scoped_ast(*guard, &vars, &Scope::default(), &declaration.reading)?;
                result.scope.merge(&value.scope);
                let resolved = if value.condition_failed || value.condition_pending {
                    None
                } else {
                    match value.known_value {
                        Some(Scalar::Bool(v)) => Some(v),
                        _ => None,
                    }
                };
                let missing = selected
                    .state
                    .missing_slot_reads
                    .take()
                    .ok_or("商のguard不足収集がない")?;
                if let Some(applies) = resolved {
                    Guard::Fixed(applies)
                } else {
                    result.missing.extend(
                        missing
                            .into_iter()
                            .filter(|f| !env.indexes.affine_valuation.contains_key(f)),
                    );
                    if !result.missing.is_empty() {
                        law.pending_expression = Some(*guard);
                        return Ok(result);
                    }
                    // Keep the full applicability fiber over the selected
                    // coordinates and original coefficient ring.
                    let mut pending = change_affine::Pending::default();
                    let computed = change_affine::numeric_guard_domain(
                        selected,
                        Some(*guard),
                        &vars,
                        &linear.axes[..dimensions],
                        &declaration.reading,
                        &mut pending,
                        ty,
                    );
                    result.scope.merge(&pending.scope);
                    result.missing.extend(pending.facts);
                    if !result.missing.is_empty() {
                        law.pending_expression = Some(*guard);
                        return Ok(result);
                    }
                    let domain = computed?;
                    if domain.particular.is_none() {
                        Guard::Fixed(false)
                    } else {
                        Guard::Affine(domain)
                    }
                }
            } else {
                Guard::Fixed(true)
            };
            let start = law.matrix.len();
            if !applies.never() {
                for operand in law.operands {
                    env.state.missing_slot_reads.replace(Some(BTreeSet::new()));
                    let value =
                        env.scoped_ast(operand, &vars, &Scope::default(), &declaration.reading)?;
                    result.scope.merge(&value.scope);
                    let symbolic = env.symbolic_source(
                        operand,
                        &vars,
                        &Scope::default(),
                        &declaration.reading,
                    )?;
                    let coordinates =
                        coefficients::view_coordinates(&symbolic, &linear.axes, ty, c)?;
                    let missing = env
                        .state
                        .missing_slot_reads
                        .take()
                        .ok_or("商のLaw不足収集がない")?;
                    if value.condition_failed || value.condition_pending || coordinates.is_none() {
                        result.missing.extend(
                            missing
                                .into_iter()
                                .filter(|f| !env.indexes.affine_valuation.contains_key(f)),
                        );
                        if !result.missing.is_empty() {
                            return Ok(result);
                        }
                        return Err(unsupported(
                            request,
                            "商のLaw値が指定係数のアフィン式でない",
                        ));
                    }
                    let (mut constants, rows) = coordinates.ok_or("商のLaw座標がない")?;
                    for (constant, row) in constants.iter_mut().zip(&rows) {
                        for (a, x) in row.iter().zip(&result.origin) {
                            *constant = coefficients::add_product(constant, a, x, c)?;
                        }
                    }
                    law.matrix.extend(coefficients::multiply(
                        ty,
                        &rows,
                        &result.embedding,
                        dimensions,
                        c,
                    )?);
                    law.offset.extend(constants);
                }
            }
            law.instances.push(Instance {
                bindings,
                guard: applies,
                rows: start..law.matrix.len(),
            });
        }
    }
    Ok(result)
}

/// 核の反例を元Assignmentへ戻し、同じ通常評価器で左右の実値を確認する。
pub(in crate::observed) fn point(
    original: &Environment<'_>,
    input: &CandidateInput,
    image: &Image,
    coordinates: &[Scalar],
    request: &Request,
    c: &mut Control,
) -> Result<quotient_evaluation::Row, ValidationFailure> {
    let law = image.law.as_ref().ok_or("アフィン商のLawがない")?;
    let linear = coefficients::Input::from_search(&input.search, c)?;
    let arithmetic_control = c.clone();
    let apply = |matrix: &Matrix,
                 offset: &[Scalar],
                 point: &[Scalar]|
     -> Result<Vec<Scalar>, ValidationFailure> {
        matrix
            .iter()
            .zip(offset)
            .map(|(row, constant)| {
                if row.len() != point.len() {
                    return Err("アフィン商の点の次元が違う".into());
                }
                let mut value = constant.clone();
                for (a, x) in row.iter().zip(point) {
                    original.tick()?;
                    value = coefficients::add_product(&value, a, x, &arithmetic_control)?;
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
    assignments.extend(linear.slots.iter().cloned().zip(values));
    let assignments = assignments.into_iter().collect::<Vec<_>>();
    let mut env = Environment::with_primitive_valuation(original.indexes.inputs, &assignments, c)?;
    env.indexes.object = Some(Arc::new(ObjectDomain::from_readings(
        original.indexes.inputs,
        input.witness.readings(),
        0,
        c,
    )?));
    let declaration = &original.indexes.inputs.law().declarations()[&law.name];
    let Signature::Law { body, .. } = &declaration.signature else {
        return Err("アフィン商のLaw署名がない".into());
    };
    let Signature::Law { guard, .. } = &declaration.signature else {
        return Err("商のLaw署名がない".into());
    };
    let expected = apply(&law.matrix, &law.offset, coordinates)?;
    let mut laws = vec![];
    for instance in &law.instances {
        env.state
            .evaluation_capture
            .replace(Some(quotient_evaluation::EvaluationCapture {
                selected: std::iter::once(*body).chain(*guard).collect(),
                nodes: vec![],
                roots: vec![],
                stack: vec![],
            }));
        let evaluated =
            finite_law_valuations::evaluate_point(&env, declaration, &instance.bindings, 0);
        let capture = env
            .state
            .evaluation_capture
            .take()
            .ok_or("商のLaw評価出現がない")?;
        let evaluated = evaluated?;
        let applicable = instance.guard.at(coordinates, &image.ty, c)?;
        if evaluated.application != Some(true)
            || evaluated.guard != Some(applicable)
            || evaluated.condition_failed
            || evaluated.condition_pending
        {
            return Err(unsupported(request, "商の反例点でLaw適用条件が変わる"));
        }
        let values = if applicable {
            let Some((_, Some(left), Some(right))) = evaluated.operands else {
                return Err("商の反例の左右値がない".into());
            };
            let flat = expected
                .get(instance.rows.clone())
                .ok_or("商のLaw成分範囲が違う")?;
            if Scalar::Tuple(vec![left.clone(), right.clone()])
                != coefficients::view_value(&Type::Tuple(vec![law.value_type.clone(); 2]), flat, c)?
            {
                return Err("商の通常Law評価とアフィン値が違う".into());
            }
            Some(Scalar::Tuple(vec![left, right]))
        } else {
            None
        };
        let body_evaluation = capture
            .roots
            .iter()
            .copied()
            .find(|i| capture.nodes[*i].expression == *body);
        let guard_evaluation = guard.and_then(|g| {
            capture
                .roots
                .iter()
                .copied()
                .find(|i| capture.nodes[*i].expression == g)
        });
        laws.push(quotient_evaluation::LawRow {
            evaluations: capture.nodes,
            body_evaluation,
            guard_evaluation,
            bindings: instance.bindings.clone(),
            guard: applicable,
            values,
            scope: evaluated.scope,
        });
    }
    let declaration = &original.indexes.inputs.law().declarations()
        [request.declaration().ok_or("アフィン商のViewがない")?];
    let Signature::View {
        body: view_body, ..
    } = &declaration.signature
    else {
        return Err("アフィン商のView署名がない".into());
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
    let view = view.known_value.ok_or("アフィン商の反例のView値がない")?;
    if view != coefficients::view_value(&image.view_type, &expected, c)? {
        return Err("アフィン商の正規形と通常View評価が違う".into());
    }
    Ok(quotient_evaluation::Row {
        parameters: Scalar::Tuple(parameters),
        image: view,
        assignments,
        laws,
    })
}

fn set_action(
    env: &mut Environment<'_>,
    slots: &[Fact],
    matrix: &Matrix,
    offset: &[Scalar],
    axes: &[affine::Parameter],
    ty: &Type,
    c: &Control,
) -> Result<(), ValidationFailure> {
    if slots.len() != matrix.len() || slots.len() != offset.len() {
        return Err("商の作用の行数が違う".into());
    }
    for ((slot, row), offset) in slots.iter().zip(matrix).zip(offset) {
        if row.len() != axes.len() {
            return Err("商の作用の列数が違う".into());
        }
        let mut form = affine::constant(offset, c)?.ok_or("アフィン商の定数がない")?;
        for (axis, coefficient) in axes.iter().zip(row) {
            let parameter = affine::parameter(ty, axis, c)?;
            let coefficient = affine::constant(coefficient, c)?;
            let term = affine::binary(BinOp::Mul, parameter.as_ref(), coefficient.as_ref(), c)?;
            form = affine::binary(BinOp::Add, Some(&form), term.as_ref(), c)?
                .ok_or("アフィン商の更新式がない")?;
        }
        env.indexes.affine_valuation.insert(slot.clone(), form);
    }
    Ok(())
}
