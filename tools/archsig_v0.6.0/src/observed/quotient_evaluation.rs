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
    pub scope: Scope,
    pub children: Vec<usize>,
}
/// 通常評価で実際に読んだ子出現だけを、子が先になる順序で受け取る。
pub(super) struct EvaluationCapture {
    pub selected: Vec<usize>,
    pub nodes: Vec<EvaluationNode>,
    pub roots: Vec<usize>,
    pub stack: Vec<Vec<usize>>,
}
pub(in crate::observed) struct LawRow {
    pub evaluations: Vec<EvaluationNode>,
    pub body_evaluation: Option<usize>,
    pub guard_evaluation: Option<usize>,
    pub bindings: Vec<(String, Scalar)>,
    pub guard: bool,
    pub values: Option<(Scalar, Scalar)>,
    pub scope: Scope,
}
pub(in crate::observed) struct Table {
    pub rows: Vec<Row>,
    pub missing: Vec<Fact>,
    pub scope: Scope,
    pub parameter_type: Type,
    pub bindings: Vec<(String, Scalar)>,
    pub law: Option<(String, Type, usize, usize)>,
}
fn unsupported(request: &Request, feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law { span: (0, 0) },
        feature: format!("{}: {feature}", request.id),
    }
}
fn exact_type(ty: &Type, c: &mut Control) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
        Ok(match ty {
            Type::Unit | Type::Bool | Type::Z | Type::Q | Type::Fp(_) | Type::Text => true,
            Type::Tuple(items) => {
                for item in items {
                    if !exact_type(item, c)? {
                        return Ok(false);
                    }
                }
                true
            }
            _ => false,
        })
    })
}
pub(in crate::observed) fn compute(
    original: &Environment<'_>,
    graph: &Graph,
    input: &CandidateInput,
    request: &Request,
    c: &mut Control,
) -> Result<Table, ValidationFailure> {
    if input.search.linear.is_some() {
        return Err(unsupported(request, "整数アフィン商の公開配送は未実装"));
    }
    let candidates = input.search.candidates.as_ref().ok_or("商の候補表がない")?;
    if !input.search.complete || !candidates.complete {
        return Err(unsupported(request, "商の有限候補全域が未確定"));
    }
    let declaration =
        &original.inputs.law().declarations[request.declaration().ok_or("商のviewがない")?];
    let Signature::View {
        params,
        returns,
        body,
    } = &declaration.signature
    else {
        return Err("商のheadがviewでない".into());
    };
    if !exact_type(returns, c)? {
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
    let law = request.arguments.iter().find(|a| a.name == "law").map(|a| {
        let Selector::Declaration { name } = &a.value else { return Err(ValidationFailure::from("商のLaw名がない")); };
        let Signature::Law { body, .. } = &original.inputs.law().declarations[name].signature else { return Err(ValidationFailure::from("商のLaw署名がない")); };
        let ExprKind::Binary { op: BinOp::Eq, lhs, rhs } = original.inputs.law().exprs[*body].kind else {
            return Err(unsupported(request, "有限商の等式以外の評価族は未実装"));
        };
        let ty = original.inputs.law().expr_type(lhs).ok_or("商の等式値型がない")?.clone();
        if !exact_type(&ty, c)? { return Err(unsupported(request, "このLaw値型の有限商は未実装")); }
        Ok((name.clone(), ty, lhs, rhs))
    }).transpose()?;
    let domain = Arc::new(ObjectDomain::from_readings(
        original.inputs,
        input.witness.readings(),
        0,
        c,
    )?);
    let mut rows = vec![];
    let mut missing = BTreeSet::new();
    let mut scope = Scope::default();
    if let Some((name, _, _, _)) = &law {
        let decl = &original.inputs.law().declarations[name];
        scope.readings.insert(decl.reading.clone());
        let Signature::Law {params, ..} = &decl.signature else {unreachable!()};
        for param in params {
            if !request.arguments.iter().any(|a| a.name == format!("bind.{}",param.name)) {
                scope.quantifiers.push(Quantifier {
                    kind:crate::law::ast::QuantKind::Forall,name:param.name.clone(),ty:param.ty.clone(),domain:None,
                    occurrence:param.span,context:None,
                });
            }
        }
    }
    for (index, candidate) in candidates.rows.iter().enumerate() {
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
        let mut env = Environment::try_primitive_valuation(original.inputs, &assignments, c)?
            .ok_or("商の候補代入が不適合")?;
        env.object = Some(domain.clone());
        env.missing_slot_reads.replace(Some(BTreeSet::new()));
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
            return Err(unsupported(request, "候補上のview適用条件の公開配送は未実装"));
        }
        let value = env.scoped_ast(*body, &vars, &Scope::default(), &declaration.reading)?;
        scope.merge(&value.scope);
        if value.condition_failed || value.condition_pending || value.known_value.is_none() {
            let reads = env.missing_slot_reads.replace(None).ok_or("商の不足位置収集がない")?;
            if !reads.is_empty() {
                missing.extend(reads);
                continue;
            }
            return Err(unsupported(request, "候補上のview構成条件・記号値の商は未実装"));
        }
        let mut laws = vec![];
        if let Some((name, _, _, _)) = &law {
            let law_decl = &original.inputs.law().declarations[name];
            let Signature::Law { params, body, guard, .. } = &law_decl.signature else { unreachable!() };
            let mut instances = vec![vec![]];
            for param in params {
                let argument = request.arguments.iter().find(|a| a.name == format!("bind.{}", param.name));
                let values = if let Some(a) = argument { vec![change_search::selector(original, graph, &a.value)?] } else {
                    let mut absent = vec![];
                    let values = change_search::domain(&env, &param.ty, param.span, &mut absent)?;
                    missing.extend(absent);
                    let Some(values) = values else { return Err(unsupported(request, "商のLaw parameter域が未確定")); };
                    values
                };
                let mut next = vec![];
                for instance in instances {
                    for scalar in &values {
                        c.checkpoint(Checkpoint::Quotient)?;
                        let mut row = instance.clone(); row.push((param.name.clone(), scalar.clone())); next.push(row);
                    }
                }
                instances = next;
            }
            for bindings in instances {
                env.evaluation_capture.replace(Some(EvaluationCapture {
                    selected:std::iter::once(*body).chain(*guard).collect(),nodes:vec![],roots:vec![],stack:vec![],
                }));
                let evaluated = finite_law_valuations::evaluate_point(&env, law_decl, &bindings, index);
                let capture = env.evaluation_capture.replace(None).ok_or("商の通常評価出現がない")?;
                let evaluated = evaluated?;
                scope.merge(&evaluated.scope);
                if evaluated.application == Some(false) { continue; }
                let values = if evaluated.guard == Some(false) { None } else {
                    match evaluated.operands {
                        Some((_, Some(left), Some(right))) => Some((left, right)),
                        _ => {
                            let reads = env.missing_slot_reads.borrow().as_ref().cloned().unwrap_or_default();
                            missing.extend(reads); missing.extend(evaluated.application_missing);
                            if missing.is_empty() { return Err(unsupported(request, "商のLaw評価族が未確定")); }
                            continue;
                        }
                    }
                };
                if evaluated.application != Some(true) || evaluated.guard.is_none() || evaluated.condition_failed || evaluated.condition_pending {
                    let reads = env.missing_slot_reads.borrow().as_ref().cloned().unwrap_or_default();
                    missing.extend(reads); missing.extend(evaluated.application_missing);
                    if missing.is_empty() { return Err(unsupported(request, "商のLaw適用条件が未確定")); }
                    continue;
                }
                let body_evaluation = capture.roots.iter().copied().find(|i| capture.nodes[*i].expression == *body);
                let guard_evaluation = guard.and_then(|id|capture.roots.iter().copied().find(|i|capture.nodes[*i].expression == id));
                laws.push(LawRow { bindings, guard: evaluated.guard == Some(true), values, scope: evaluated.scope,
                    evaluations:capture.nodes,body_evaluation,guard_evaluation });
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
                if !bindings.iter().any(|(n,_)| n == name) {
                    bindings.push((name.into(),change_search::selector(original,graph,&argument.value)?));
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
