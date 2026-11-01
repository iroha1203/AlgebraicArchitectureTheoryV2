//! 同じ候補状態の通常view評価から有限な全fiberを作る。
use super::*;
use crate::law::model::Signature;
use crate::observed::{
    change_result::CandidateInput, object_evaluate::ObjectDomain, projection::ProjectionType,
};
use std::sync::Arc;
pub(in crate::observed) struct Row {
    pub parameters: Scalar,
    pub image: Scalar,
    pub assignments: Vec<(Fact, Scalar)>,
    pub laws: Vec<LawRow>,
}
pub(in crate::observed) struct EvaluationNode {
    pub expression: usize,
    pub bindings: Vec<(String, Scalar)>,
    pub value: Option<Scalar>,
    pub residual: Option<Scalar>,
    pub scope: Scope,
    pub children: Vec<usize>,
    pub finite_bindings: Option<Vec<Scalar>>,
}
/// 通常評価で実際に読んだ子出現だけを、子が先になる順序で受け取る。
#[derive(Default)]
pub(super) struct EvaluationFrame {
    pub children: Vec<usize>,
    pub finite_bindings: Option<Vec<Scalar>>,
}
pub(super) struct EvaluationCapture {
    pub selected: Vec<usize>,
    pub nodes: Vec<EvaluationNode>,
    pub roots: Vec<usize>,
    pub stack: Vec<EvaluationFrame>,
}
pub(in crate::observed) struct LawRow {
    pub evaluations: Vec<EvaluationNode>,
    pub body_evaluation: Option<usize>,
    pub guard_evaluation: Option<usize>,
    pub bindings: Vec<(String, Scalar)>,
    pub guard: bool,
    pub values: Option<Scalar>,
    pub scope: Scope,
}
pub(in crate::observed) struct Table {
    pub rows: Vec<Row>,
    pub missing: Vec<Fact>,
    pub scope: Scope,
    pub parameter_type: Type,
    pub bindings: Vec<(String, Scalar)>,
    pub law: Option<(String, Type)>,
}
fn unsupported(request: &Request, feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law { span: (0, 0) },
        feature: format!("{}: {feature}", request.id),
    }
}
fn exact_type(
    ty: &Type,
    law: &crate::law::CheckedLaw,
    c: &mut Control,
) -> Result<bool, ValidationFailure> {
    fn visit(
        ty: &Type,
        law: &crate::law::CheckedLaw,
        c: &mut Control,
        active: &mut Vec<String>,
    ) -> Result<bool, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            c.checkpoint(Checkpoint::PrimitiveValuation)?;
            Ok(match ty {
                Type::Unit | Type::Bool | Type::Z | Type::Q | Type::Fp(_) | Type::Text => true,
                Type::Option(item) | Type::List(item) | Type::Set(item) => {
                    visit(item, law, c, active)?
                }
                Type::Tuple(items) => {
                    for item in items {
                        if !visit(item, law, c, active)? {
                            return Ok(false);
                        }
                    }
                    true
                }
                Type::Data(family) => {
                    if active.contains(family) {
                        // 定義検査済みの正の自己参照。有限な実値の比較はdata::equalが行う。
                        return Ok(true);
                    }
                    let constructors = data::constructors(law, family)?;
                    active.push(family.clone());
                    let result: Result<bool, ValidationFailure> = (|| {
                        for constructor in constructors {
                            c.checkpoint(Checkpoint::PrimitiveValuation)?;
                            for argument in &constructor.arguments {
                                if !visit(argument, law, c, active)? {
                                    return Ok(false);
                                }
                            }
                        }
                        Ok(true)
                    })();
                    active.pop();
                    result?
                }
                _ => false,
            })
        })
    }
    visit(ty, law, c, &mut vec![])
}

/// Project only the declared logical structure from normal evaluation occurrences.
/// Calls and non-equality Bool expressions expose their return value.
fn observation(
    law: &crate::law::CheckedLaw,
    expression: usize,
    occurrence: Option<usize>,
    nodes: &[EvaluationNode],
    c: &mut Control,
) -> Result<(Type, Option<Scalar>), ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        c.checkpoint(Checkpoint::Quotient)?;
        let unsupported = |feature: &str| ValidationFailure::UnsupportedExpression {
            location: Location::Law {
                span: law.exprs[expression].span,
            },
            feature: feature.into(),
        };
        let node = occurrence.map(|i| &nodes[i]);
        let child = |id| {
            node.and_then(|n| {
                n.children
                    .iter()
                    .copied()
                    .find(|i| nodes[*i].expression == id)
            })
        };
        match &law.exprs[expression].kind {
            ExprKind::Group(body) | ExprKind::Let { body, .. } => {
                observation(law, *body, child(*body), nodes, c)
            }
            ExprKind::Binary {
                op: BinOp::Eq,
                lhs,
                rhs,
            } => {
                let ty = law.expr_type(*lhs).ok_or("商の等式値型がない")?.clone();
                if !exact_type(&ty, law, c)? {
                    return Err(unsupported("商の等式値型が未対応"));
                }
                let value = child(*lhs)
                    .and_then(|i| nodes[i].value.clone())
                    .zip(child(*rhs).and_then(|i| nodes[i].value.clone()))
                    .map(|(l, r)| Scalar::Tuple(vec![l, r]));
                Ok((Type::Tuple(vec![ty.clone(), ty]), value))
            }
            ExprKind::Match { scrutinee, arms } => {
                let ty = law
                    .expr_type(*scrutinee)
                    .ok_or("match判別値型がない")?
                    .clone();
                if !exact_type(&ty, law, c)? {
                    return Err(unsupported("このmatch判別値型の商は未実装"));
                }
                let input = child(*scrutinee).and_then(|i| nodes[i].value.as_ref());
                let selected = data::select(law, expression, input, c)?;
                let (observed_type, observed) = if ty == Type::Bool {
                    observation(law, *scrutinee, child(*scrutinee), nodes, c)?
                } else {
                    (ty, input.cloned())
                };
                let mut types = vec![observed_type];
                let mut complete = observed.is_some();
                let mut values = observed.into_iter().collect::<Vec<_>>();
                complete &= node.is_some_and(|n| n.value.is_some()) && selected.is_some();
                if let Some(node) = node {
                    complete &= node
                        .children
                        .iter()
                        .filter(|i| arms.iter().any(|arm| arm.body == nodes[**i].expression))
                        .count()
                        == 1;
                }
                for (index, arm) in arms.iter().enumerate() {
                    let selected_here = selected == Some(index);
                    let occurrence = if selected_here { child(arm.body) } else { None };
                    let (ty, value) = observation(law, arm.body, occurrence, nodes, c)?;
                    if selected_here {
                        complete &= value.is_some();
                        if let (Some(input), Some(occurrence)) = (input, occurrence) {
                            for (name, expected) in
                                data::bindings(law, expression, index, input, c)?
                            {
                                let actual = nodes[occurrence]
                                    .bindings
                                    .iter()
                                    .find(|(n, _)| *n == name)
                                    .map(|(_, v)| v);
                                complete &= match actual {
                                    Some(actual) => data::equal(&expected, actual, c)?,
                                    None => false,
                                };
                            }
                        } else {
                            complete = false;
                        }
                    }
                    types.push(Type::Option(Box::new(ty.clone())));
                    values.push(Scalar::Option {
                        element: ty,
                        value: value.map(Box::new),
                    });
                }
                Ok((
                    Type::Tuple(types),
                    complete.then_some(Scalar::Tuple(values)),
                ))
            }
            ExprKind::Quant { .. } => {
                let spec = quantifier::spec(law, expression, c)?;
                let (body_type, _) = observation(law, spec.body, None, nodes, c)?;
                let element = Type::Tuple(vec![spec.element, body_type]);
                let mut items = vec![];
                let mut complete =
                    node.is_some_and(|n| n.value.is_some() && n.finite_bindings.is_some());
                if let Some(node) = node {
                    for i in &node.children {
                        if nodes[*i].expression != spec.body {
                            continue;
                        }
                        let (_, value) = observation(law, spec.body, Some(*i), nodes, c)?;
                        let binding = nodes[*i]
                            .bindings
                            .iter()
                            .find(|(n, _)| n == spec.name)
                            .map(|(_, v)| v.clone());
                        if let Some((binding, value)) = binding.zip(value) {
                            items.push(Scalar::Tuple(vec![binding, value]));
                        } else {
                            complete = false;
                        }
                    }
                }
                if let Some(expected) = node.and_then(|n| n.finite_bindings.as_ref()) {
                    complete &= expected.len() == items.len();
                    for (expected, actual) in expected.iter().zip(&items) {
                        let Scalar::Tuple(pair) = actual else {
                            unreachable!()
                        };
                        complete &= data::equal(expected, &pair[0], c)?;
                    }
                }
                let value = if complete {
                    Some(data::set(element.clone(), &items, c)?)
                } else {
                    None
                };
                Ok((Type::Set(Box::new(element)), value))
            }
            kind => {
                let children = match kind {
                    ExprKind::Binary {
                        op: BinOp::And | BinOp::Or | BinOp::Implies,
                        lhs,
                        rhs,
                    } => vec![*lhs, *rhs],
                    ExprKind::Unary {
                        op: crate::law::ast::UnOp::Not,
                        operand,
                    } => vec![*operand],
                    ExprKind::If {
                        cond,
                        then_branch,
                        else_branch,
                    } => vec![*cond, *then_branch, *else_branch],
                    _ => vec![],
                };
                if children.is_empty() {
                    return Ok((Type::Bool, node.and_then(|n| n.value.clone())));
                }
                let mut types = vec![];
                let mut values = vec![];
                let mut complete = node.is_some_and(|n| n.value.is_some());
                for id in children {
                    let needed = match kind {
                        ExprKind::If {
                            cond,
                            then_branch,
                            else_branch,
                        } if id != *cond => {
                            match child(*cond).and_then(|i| nodes[i].value.as_ref()) {
                                Some(Scalar::Bool(true)) => id == *then_branch,
                                Some(Scalar::Bool(false)) => id == *else_branch,
                                _ => true,
                            }
                        }
                        ExprKind::Binary { op, lhs, rhs } if id == *rhs => !matches!(
                            (op, child(*lhs).and_then(|i| nodes[i].value.as_ref())),
                            (BinOp::And | BinOp::Implies, Some(Scalar::Bool(false)))
                                | (BinOp::Or, Some(Scalar::Bool(true)))
                        ),
                        _ => true,
                    };
                    let (ty, value) =
                        observation(law, id, if needed { child(id) } else { None }, nodes, c)?;
                    complete &= !needed || value.is_some();
                    types.push(Type::Option(Box::new(ty.clone())));
                    values.push(Scalar::Option {
                        element: ty,
                        value: value.map(Box::new),
                    });
                }
                Ok((
                    Type::Tuple(types),
                    complete.then_some(Scalar::Tuple(values)),
                ))
            }
        }
    })
}

pub(in crate::observed) fn compute(
    original: &Environment<'_>,
    graph: &Graph,
    input: &CandidateInput,
    request: &Request,
    c: &mut Control,
) -> Result<Table, ValidationFailure> {
    if input.search.linear.is_some() || input.search.rational.is_some() {
        return Err(unsupported(
            request,
            "この係数体のアフィン商の公開配送は未実装",
        ));
    }
    let candidates = input.search.candidates.as_ref().ok_or("商の候補表がない")?;
    if !input.search.complete || !candidates.complete {
        return Err(unsupported(request, "商の有限候補全域が未確定"));
    }
    let declaration =
        &original.indexes.inputs.law().declarations[request.declaration().ok_or("商のviewがない")?];
    let Signature::View {
        params,
        returns,
        body,
    } = &declaration.signature
    else {
        return Err("商のheadがviewでない".into());
    };
    if !exact_type(returns, original.indexes.inputs.law(), c)? {
        return Err(unsupported(request, "このview型の有限商の等値は未実装"));
    }
    let bindings = params
        .iter()
        .map(|p| {
            let arg = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
                .ok_or("商のview束縛がない")?;
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
        .map(|a| {
            let Selector::Declaration { name } = &a.value else {
                return Err(ValidationFailure::from("商のLaw名がない"));
            };
            let Signature::Law { body, .. } = &original.indexes.inputs.law().declarations[name].signature
            else {
                return Err(ValidationFailure::from("商のLaw署名がない"));
            };
            let (ty, _) = observation(original.indexes.inputs.law(), *body, None, &[], c)?;
            Ok((name.clone(), ty))
        })
        .transpose()?;
    let domain = Arc::new(ObjectDomain::from_readings(
        original.indexes.inputs,
        input.witness.readings(),
        0,
        c,
    )?);
    let mut rows = vec![];
    let mut missing = BTreeSet::new();
    let mut scope = Scope::default();
    if let Some((name, _)) = &law {
        let decl = &original.indexes.inputs.law().declarations[name];
        scope.readings.insert(decl.reading.clone());
        let Signature::Law { params, .. } = &decl.signature else {
            unreachable!()
        };
        for param in params {
            if !request
                .arguments
                .iter()
                .any(|a| a.name == format!("bind.{}", param.name))
            {
                scope.quantifiers.push(Quantifier {
                    kind: crate::law::ast::QuantKind::Forall,
                    name: param.name.clone(),
                    ty: param.ty.clone(),
                    domain: None,
                    occurrence: param.span,
                    context: None,
                });
            }
        }
    }
    'candidates: for (index, candidate) in candidates.rows.iter().enumerate() {
        c.checkpoint(Checkpoint::Quotient)?;
        if candidate.update.state == change_evaluation::State::Excluded {
            continue;
        }
        if matches!(input.domain_type, ProjectionType::SolutionSet(_)) {
            match input
                .search
                .solutions
                .iter()
                .find(|row| row.candidate == index)
                .and_then(|row| row.member)
            {
                Some(false) => continue,
                Some(true) => {}
                None => return Err(unsupported(request, "商の解所属が未確定")),
            }
        }
        if candidate.update.state != change_evaluation::State::Ready {
            return Err(unsupported(request, "商の候補状態が未確定"));
        }
        let mut assignments = input
            .assignments
            .iter()
            .cloned()
            .collect::<BTreeMap<_, _>>();
        assignments.extend(candidate.update.values.iter().cloned());
        let assignments = assignments.into_iter().collect::<Vec<_>>();
        let mut env = Environment::try_primitive_valuation(original.indexes.inputs, &assignments, c)?
            .ok_or("商の候補代入が不適合")?;
        env.indexes.object = Some(domain.clone());
        env.state.missing_slot_reads.replace(Some(BTreeSet::new()));
        let mut checked = BTreeMap::new();
        let mut checks = owned_call::Checks::default();
        let mut vars = BTreeMap::new();
        for (param, (name, value)) in params.iter().zip(&bindings) {
            env.owned_call_value_check(
                &param.ty,
                &crate::observed::term::affine::Value::Known(value.clone()),
                &checked,
                &declaration.reading,
                declaration.span,
                &mut checks,
            )?;
            checked.insert(name.as_str(), Some(value));
            vars.insert(
                name.clone(),
                SourceValue {
                    known_value: Some(value.clone()),
                    scalar_scope: Some(Scope::default()),
                    scope: Scope::default(),
                    support: vec![],
                    condition_failed: false,
                    condition_pending: false,
                    symbolic: None,
                    comparison: None,
                    affine: None,
                },
            );
        }
        scope.merge(&checks.scope);
        if checks.failure.is_some() || checks.blocked {
            if !checks.missing.is_empty() {
                missing.extend(checks.missing);
                continue;
            }
            return Err(unsupported(
                request,
                "候補上のview適用条件の公開配送は未実装",
            ));
        }
        let value = env.scoped_ast(*body, &vars, &Scope::default(), &declaration.reading)?;
        scope.merge(&value.scope);
        if value.condition_failed || value.condition_pending || value.known_value.is_none() {
            let reads = env
                .state.missing_slot_reads
                .replace(None)
                .ok_or("商の不足位置収集がない")?;
            if !reads.is_empty() {
                missing.extend(reads);
                continue;
            }
            return Err(unsupported(
                request,
                "候補上のview構成条件・記号値の商は未実装",
            ));
        }
        let mut laws = vec![];
        if let Some((name, _)) = &law {
            let law_decl = &original.indexes.inputs.law().declarations[name];
            let Signature::Law {
                params,
                body,
                guard,
                ..
            } = &law_decl.signature
            else {
                unreachable!()
            };
            let mut instances = vec![vec![]];
            for param in params {
                let argument = request
                    .arguments
                    .iter()
                    .find(|a| a.name == format!("bind.{}", param.name));
                let values = if let Some(a) = argument {
                    vec![change_search::selector(original, graph, &a.value)?]
                } else {
                    let mut absent = vec![];
                    let values = change_search::domain(&env, &param.ty, param.span, &mut absent)?;
                    missing.extend(absent);
                    let Some(values) = values else {
                        if !missing.is_empty() {
                            break 'candidates;
                        }
                        return Err(unsupported(request, "商のLaw parameter域が未確定"));
                    };
                    values
                };
                let mut next = vec![];
                for instance in instances {
                    for scalar in &values {
                        c.checkpoint(Checkpoint::Quotient)?;
                        let mut row = instance.clone();
                        row.push((param.name.clone(), scalar.clone()));
                        next.push(row);
                    }
                }
                instances = next;
            }
            for bindings in instances {
                env.state.evaluation_capture.replace(Some(EvaluationCapture {
                    selected: std::iter::once(*body).chain(*guard).collect(),
                    nodes: vec![],
                    roots: vec![],
                    stack: vec![],
                }));
                let evaluated =
                    finite_law_valuations::evaluate_point(&env, law_decl, &bindings, index);
                let capture = env
                    .state.evaluation_capture
                    .replace(None)
                    .ok_or("商の通常評価出現がない")?;
                let evaluated = evaluated?;
                scope.merge(&evaluated.scope);
                if evaluated.application == Some(false) {
                    continue;
                }
                let body_evaluation = capture
                    .roots
                    .iter()
                    .copied()
                    .find(|i| capture.nodes[*i].expression == *body);
                let values = if evaluated.guard == Some(false) {
                    None
                } else {
                    let (_, value) =
                        observation(env.indexes.inputs.law(), *body, body_evaluation, &capture.nodes, c)?;
                    match value {
                        Some(value) => Some(value),
                        _ => {
                            let reads = env
                                .state.missing_slot_reads
                                .borrow()
                                .as_ref()
                                .cloned()
                                .unwrap_or_default();
                            missing.extend(reads);
                            missing.extend(evaluated.application_missing);
                            if missing.is_empty() {
                                return Err(unsupported(request, "商のLaw評価族が未確定"));
                            }
                            continue;
                        }
                    }
                };
                if evaluated.application != Some(true)
                    || evaluated.guard.is_none()
                    || evaluated.condition_failed
                    || evaluated.condition_pending
                {
                    let reads = env
                        .state.missing_slot_reads
                        .borrow()
                        .as_ref()
                        .cloned()
                        .unwrap_or_default();
                    missing.extend(reads);
                    missing.extend(evaluated.application_missing);
                    if missing.is_empty() {
                        return Err(unsupported(request, "商のLaw適用条件が未確定"));
                    }
                    continue;
                }
                let guard_evaluation = guard.and_then(|id| {
                    capture
                        .roots
                        .iter()
                        .copied()
                        .find(|i| capture.nodes[*i].expression == id)
                });
                laws.push(LawRow {
                    bindings,
                    guard: evaluated.guard == Some(true),
                    values,
                    scope: evaluated.scope,
                    evaluations: capture.nodes,
                    body_evaluation,
                    guard_evaluation,
                });
            }
        }
        rows.push(Row {
            assignments: if law.is_some() { assignments } else { vec![] },
            laws,
            parameters: Scalar::Tuple(candidate.parameters.clone()),
            image: value.known_value.ok_or("検査済みview値がない")?,
        });
    }
    let mut bindings = bindings;
    if law.is_some() {
        for argument in &request.arguments {
            if let Some(name) = argument.name.strip_prefix("bind.") {
                if !bindings.iter().any(|(n, _)| n == name) {
                    bindings.push((
                        name.into(),
                        change_search::selector(original, graph, &argument.value)?,
                    ));
                }
            }
        }
    }
    Ok(Table {
        rows,
        missing: missing.into_iter().collect(),
        scope,
        parameter_type: Type::Tuple(candidates.parameter_types.clone()),
        bindings,
        law,
    })
}

#[cfg(test)]
mod tests;
