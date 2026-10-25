//! 明示localの単一instanceが公開する直接読取り。依存と読取り権限を分ける。
use super::*;
use crate::observed::{build_result::Builder, change_result, local_result};
use crate::{
    canonical::Json,
    law::model::{Declaration, Signature},
};

pub(in crate::observed) struct Context {
    pub locals: Vec<Json>,
    pub carrier: Vec<Json>,
    pub positions: Vec<Fact>,
    pub readings: Vec<Json>,
    pub arguments: Vec<NodeRef>,
    pub reasons: Vec<Reason>,
    pub scope: Scope,
}
fn unsupported(span: (usize, usize), feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law { span },
        feature: feature.into(),
    }
}
fn known(value: Scalar) -> SourceValue {
    SourceValue {
        condition_failed: false,
        condition_pending: false,
        symbolic: None,
        comparison: None,
        scope: Scope::default(),
        known_value: Some(value),
        affine: None,
        support: vec![],
        scalar_scope: Some(Scope::default()),
    }
}
fn subject_carrier(value: &Scalar, carrier: &mut Vec<Json>) {
    if matches!(value, Scalar::Subject { .. }) {
        carrier.push(Json::obj([
            ("type", value.ty().wire()),
            ("value", value.wire()),
        ]));
    }
}
fn positions(facts: &[Fact]) -> impl Iterator<Item = Fact> + '_ {
    facts.iter().filter(|f| f.field.is_some()).map(|f| Fact {
        atom: None,
        ..f.clone()
    })
}
fn evaluate_read(
    env: &Environment<'_>,
    id: usize,
    variables: &BTreeMap<String, SourceValue>,
    scope: &Scope,
    reading: &str,
) -> Result<(SourceValue, Vec<Fact>, Vec<Fact>), ValidationFailure> {
    let outer_missing = env.missing_slot_reads.replace(Some(BTreeSet::new()));
    let outer_reads = env.primitive_reads.replace(Some(BTreeSet::new()));
    let value = env.scoped_ast(id, variables, scope, reading);
    let reads = env
        .primitive_reads
        .replace(outer_reads)
        .ok_or("localの読取り収集がない")?;
    let missing = env
        .missing_slot_reads
        .replace(outer_missing)
        .ok_or("localの欠測収集がない")?;
    if let Some(outer) = env.primitive_reads.borrow_mut().as_mut() {
        outer.extend(reads.iter().cloned());
    }
    if let Some(outer) = env.missing_slot_reads.borrow_mut().as_mut() {
        outer.extend(missing.iter().cloned());
    }
    Ok((
        value?,
        reads.into_iter().collect(),
        missing
            .into_iter()
            .filter(|f| {
                !env.primitive_valuation
                    .as_ref()
                    .is_some_and(|v| v.contains_key(f))
            })
            .collect(),
    ))
}
fn bound_name<'a>(env: &'a Environment<'_>, id: usize) -> Option<&'a str> {
    match &env.inputs.law().exprs[id].kind {
        ExprKind::Group(child) => bound_name(env, *child),
        ExprKind::Dotted(parts) if parts.len() == 1 => Some(parts[0].name.as_str()),
        _ => None,
    }
}
fn visible_slot(
    env: &Environment<'_>,
    id: usize,
    bindings: &[(String, Scalar)],
) -> Result<Option<Fact>, ValidationFailure> {
    let expr = &env.inputs.law().exprs[id];
    let (variable, field) = match &expr.kind {
        ExprKind::Group(child) => return visible_slot(env, *child, bindings),
        ExprKind::Dotted(parts) if parts.len() == 2 => {
            (parts[0].name.as_str(), parts[1].name.as_str())
        }
        ExprKind::Field { base, name } => (
            bound_name(env, *base)
                .ok_or_else(|| unsupported(expr.span, "明示localの複合field読取りは未実装"))?,
            name.name.as_str(),
        ),
        ExprKind::Dotted(parts)
            if parts.len() == 1 && bindings.iter().any(|(n, _)| n == &parts[0].name) =>
        {
            return Ok(None);
        }
        ExprKind::Bool(_) | ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Unit => {
            return Ok(None);
        }
        _ => {
            return Err(unsupported(
                expr.span,
                "明示localの複合読取りの因子分解は未実装",
            ));
        }
    };
    let Some((
        _,
        Scalar::Subject {
            snapshot,
            subject,
            entity,
        },
    )) = bindings.iter().find(|(n, _)| n == variable)
    else {
        return Err(unsupported(
            expr.span,
            "明示localの直接読取り元が参照でない",
        ));
    };
    Ok(Some(Fact {
        snapshot: snapshot.clone(),
        subject: subject.clone(),
        field: Some(format!("{entity}.{field}")),
        atom: None,
    }))
}
fn reason(
    context: &mut Context,
    request: &Request,
    kind: ReasonKind,
    missing: Vec<Fact>,
    span: (usize, usize),
    dependencies: Vec<NodeRef>,
) {
    context.reasons.push(Reason {
        kind,
        request: request.id.clone(),
        dependencies,
        missing,
        location: Some(Location::Law { span }),
    });
}
pub(in crate::observed) fn materialize(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    declaration: &Declaration,
    request: &Request,
    required_carrier: &[Json],
    required_positions: &[Fact],
    coordinates: &[NodeRef],
    c: &mut Control,
) -> Result<Context, ValidationFailure> {
    let Signature::Local {
        params,
        guard,
        reads,
    } = &declaration.signature
    else {
        return Err("局所読取りの元宣言がlocalでない".into());
    };
    let mut out = Context {
        locals: vec![],
        carrier: vec![],
        positions: vec![],
        readings: vec![],
        arguments: vec![],
        reasons: vec![],
        scope: Scope::default(),
    };
    let visibility = || ReasonKind::VisibilityInsufficient {
        locals: vec![declaration.name.clone()],
        coordinates: coordinates.to_vec(),
    };
    let mut bindings = vec![];
    let mut absent = vec![];
    for p in params {
        c.checkpoint(Checkpoint::Localize)?;
        let values = change_search::domain(env, &p.ty, p.span, &mut absent)?;
        let Some(mut values) = values else {
            reason(
                &mut out,
                request,
                ReasonKind::Missing,
                absent,
                declaration.span,
                coordinates.to_vec(),
            );
            return Ok(out);
        };
        if values.is_empty() {
            reason(
                &mut out,
                request,
                visibility(),
                vec![],
                declaration.span,
                coordinates.to_vec(),
            );
            return Ok(out);
        }
        if values.len() != 1 {
            return Err(unsupported(
                declaration.span,
                "明示localの複数instanceのcoverは未実装",
            ));
        }
        bindings.push((p.name.clone(), values.remove(0)));
    }
    let mut checks = owned_call::Checks::default();
    let mut owner_values = BTreeMap::new();
    for (p, (_, v)) in params.iter().zip(&bindings) {
        env.owned_call_value_check(
            &p.ty,
            &super::super::term::affine::Value::Known(v.clone()),
            &owner_values,
            &declaration.reading,
            declaration.span,
            &mut checks,
        )?;
        owner_values.insert(p.name.as_str(), Some(v));
    }
    out.scope.merge(&checks.scope);
    out.positions.extend(positions(&checks.support));
    if checks.failure.is_some() {
        reason(
            &mut out,
            request,
            visibility(),
            vec![],
            declaration.span,
            coordinates.to_vec(),
        );
        return Ok(out);
    }
    absent.extend(checks.missing);
    if checks.blocked || !absent.is_empty() {
        if absent.is_empty() {
            return Err(unsupported(declaration.span, "localの所属条件が未確定"));
        }
        reason(
            &mut out,
            request,
            ReasonKind::Missing,
            absent,
            declaration.span,
            coordinates.to_vec(),
        );
        return Ok(out);
    }
    let variables = bindings
        .iter()
        .map(|(n, v)| (n.clone(), known(v.clone())))
        .collect();
    let node_bindings = bindings
        .iter()
        .map(|(n, v)| Ok((n.clone(), change_result::value(b, v)?)))
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    for (_, v) in &bindings {
        subject_carrier(v, &mut out.carrier);
    }
    out.arguments.extend(node_bindings.iter().map(|(_, r)| *r));
    let mut scope = Scope::default();
    scope.readings.insert(declaration.reading.clone());
    if let Some(id) = guard {
        let expression = change_result::source_expression(b, env, *id, &node_bindings, &[])?;
        let (value, dependencies, absent) =
            evaluate_read(env, *id, &variables, &scope, &declaration.reading)?;
        b.parts[expression.0 - b.base].scope.merge(&value.scope);
        out.scope.merge(&value.scope);
        out.positions.extend(dependencies);
        out.arguments.push(expression);
        if value.condition_failed {
            return Err(unsupported(
                declaration.span,
                "local guardの式の適用条件が不成立",
            ));
        }
        if value.condition_pending || value.known_value.is_none() {
            if absent.is_empty() {
                return Err(unsupported(declaration.span, "local guardが未確定"));
            }
            reason(
                &mut out,
                request,
                ReasonKind::Missing,
                absent,
                declaration.span,
                vec![expression],
            );
            return Ok(out);
        }
        if value.known_value == Some(Scalar::Bool(false)) {
            let dependencies = std::iter::once(expression)
                .chain(coordinates.iter().copied())
                .collect();
            reason(
                &mut out,
                request,
                visibility(),
                vec![],
                declaration.span,
                dependencies,
            );
            return Ok(out);
        }
        if value.known_value != Some(Scalar::Bool(true)) {
            return Err("local guardがBoolでない".into());
        }
    }
    let mut visible = vec![];
    for id in reads {
        c.checkpoint(Checkpoint::Localize)?;
        visible.extend(visible_slot(env, *id, &bindings)?);
        let expression = change_result::source_expression(b, env, *id, &node_bindings, &[])?;
        let (read, dependencies, absent) =
            evaluate_read(env, *id, &variables, &scope, &declaration.reading)?;
        b.parts[expression.0 - b.base].scope.merge(&read.scope);
        out.scope.merge(&read.scope);
        out.positions.extend(dependencies);
        out.arguments.push(expression);
        if read.condition_failed {
            return Err(unsupported(
                declaration.span,
                "local読取りの式の適用条件が不成立",
            ));
        }
        if read.condition_pending || read.known_value.is_none() {
            if absent.is_empty() {
                return Err(unsupported(declaration.span, "localの読取り値が未確定"));
            }
            reason(
                &mut out,
                request,
                ReasonKind::Missing,
                absent,
                declaration.span,
                vec![expression],
            );
            continue;
        }
        let value = read.known_value.ok_or("localの確定値がない")?;
        subject_carrier(&value, &mut out.carrier);
        let actual = change_result::value(b, &value)?;
        let image = local_result::domain(b, &value.ty(), &[actual])?;
        out.readings.push(Json::obj([
            ("expression", expression.wire()),
            ("type", value.ty().wire()),
            ("domain", image.wire()),
        ]));
        out.arguments.push(image);
    }
    out.carrier.sort_by_key(Json::canonical);
    out.carrier.dedup();
    out.positions.sort();
    out.positions.dedup();
    if required_positions.iter().any(|f| !visible.contains(f))
        || required_carrier.iter().any(|v| !out.carrier.contains(v))
    {
        reason(
            &mut out,
            request,
            visibility(),
            vec![],
            declaration.span,
            coordinates.to_vec(),
        );
    }
    out.locals.push(Json::obj([
        ("declaration", Json::str(&declaration.name)),
        (
            "bindings",
            Json::Arr(
                node_bindings
                    .iter()
                    .map(|(n, r)| Json::obj([("name", Json::str(n)), ("value", r.wire())]))
                    .collect(),
            ),
        ),
    ]));
    Ok(out)
}
