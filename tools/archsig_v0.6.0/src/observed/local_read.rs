//! 明示localの各instanceが公開する直接読取り。依存と読取り権限を分ける。
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
    pub visible: Vec<Fact>,
    pub read_supports: Vec<local_result::geometry::Support>,
    pub read_refs: Vec<NodeRef>,
    pub projections: Vec<local_result::geometry::Projection>,
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
fn subject_carrier(
    value: &Scalar,
    carrier: &mut Vec<Json>,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        c.checkpoint(Checkpoint::Localize)?;
        match value {
            Scalar::Subject { .. } => carrier.push(Json::obj([
                ("type", value.ty().wire()),
                ("value", value.wire()),
            ])),
            Scalar::Tuple(items) => pending.extend(items.iter().rev()),
            _ => {}
        }
    }
    Ok(())
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
/// 暗黙contextの公開読取りを、その式が実際に参照する位置へ制限する。
pub(in crate::observed) fn implicit_support(
    env: &Environment<'_>,
    id: usize,
    bindings: &[(String, Scalar)],
    reading: &str,
    c: &mut Control,
) -> Result<(Vec<Json>, Vec<Fact>), ValidationFailure> {
    let variables = bindings
        .iter()
        .map(|(n, v)| (n.clone(), known(v.clone())))
        .collect();
    let (value, reads, missing) = evaluate_read(env, id, &variables, &Scope::default(), reading)?;
    if !missing.is_empty() {
        return Err("確定した暗黙読取りに欠測がある".into());
    }
    let mut carrier = vec![];
    for (_, value) in bindings {
        subject_carrier(value, &mut carrier, c)?;
    }
    if let Some(value) = value.known_value {
        subject_carrier(&value, &mut carrier, c)?;
    }
    for fact in &reads {
        let subject = env.subject(&fact.snapshot, &fact.subject)?;
        subject_carrier(
            &Scalar::Subject {
                snapshot: fact.snapshot.clone(),
                subject: fact.subject.clone(),
                entity: subject.ty.clone(),
            },
            &mut carrier,
            c,
        )?;
    }
    carrier.sort_by_key(Json::canonical);
    carrier.dedup();
    let mut dependencies = positions(&reads).collect::<Vec<_>>();
    dependencies.sort();
    dependencies.dedup();
    Ok((carrier, dependencies))
}
pub(in crate::observed) fn read_bindings(
    env: &Environment<'_>,
    id: usize,
    bindings: &[(String, Scalar)],
    c: &mut Control,
) -> Result<Vec<(String, Scalar)>, ValidationFailure> {
    let mut names = BTreeSet::new();
    let mut pending = vec![id];
    while let Some(id) = pending.pop() {
        c.checkpoint(Checkpoint::Localize)?;
        match &env.inputs.law().exprs[id].kind {
            ExprKind::Group(child)
            | ExprKind::Field { base: child, .. }
            | ExprKind::Unary { operand: child, .. } => pending.push(*child),
            ExprKind::Binary { lhs, rhs, .. } => pending.extend([*lhs, *rhs]),
            ExprKind::If { cond, then_branch, else_branch } => {
                pending.extend([*cond, *then_branch, *else_branch]);
            }
            ExprKind::Tuple(items) => pending.extend(items),
            ExprKind::Dotted(parts) => {
                if let Some(first) = parts.first() {
                    names.insert(first.name.as_str());
                }
            }
            ExprKind::Bool(_) | ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Unit => {}
            _ => return Ok(bindings.to_vec()),
        }
    }
    Ok(bindings
        .iter()
        .filter(|(name, _)| names.contains(name.as_str()))
        .cloned()
        .collect())
}
// Tuple全体を読めない交差でだけ使う成分。公開ノードは必要になるまで作らない。
fn projections(
    env: &Environment<'_>,
    id: usize,
    value: &Scalar,
    read: usize,
    bindings: &[(String, Scalar)],
    reading: &str,
    out: &mut Vec<local_result::geometry::Projection>,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let mut pending = vec![(id, value, vec![])];
    while let Some((id, value, path)) = pending.pop() {
        c.checkpoint(Checkpoint::Localize)?;
        match (&env.inputs.law().exprs[id].kind, value) {
            (ExprKind::Group(child), _) => pending.push((*child, value, path)),
            (ExprKind::Tuple(items), Scalar::Tuple(values)) => {
                for (i, (child, value)) in items.iter().zip(values).enumerate().rev() {
                    let mut child_path = path.clone();
                    child_path.push(i);
                    pending.push((*child, value, child_path));
                }
            }
            _ if field_path(env, id)?.is_some_and(|(_, fields)| fields.len() > 1) => {
                let slots = visible_slots(env, id, bindings, reading)?;
                let slot = slots.first().ok_or("参照経路の末端slotがない")?;
                let owner = env.subject(&slot.snapshot, &slot.subject)?;
                let subject = Scalar::Subject { snapshot: slot.snapshot.clone(),
                    subject: slot.subject.clone(), entity: owner.ty.clone() };
                let declaration = &env.inputs.definitions().declarations[&owner.ty];
                let (params, fields) = declaration.signature.record_fields().ok_or("末端fieldのrecordがない")?;
                let field = params.iter().chain(fields).find(|f|
                    slot.field.as_ref() == Some(&format!("{}.{}", owner.ty, f.name)))
                    .ok_or("末端fieldの宣言がない")?;
                let mut carrier = vec![];
                subject_carrier(value, &mut carrier, c)?;
                out.push(local_result::geometry::Projection {
                    read, path, field: Some((subject, field.location.clone())), values: vec![value.clone()],
                    support: local_result::geometry::Support {
                        carrier, positions: slots.clone(), visible: slots,
                    },
                });
            }
            _ if !path.is_empty() => {
                // 成分を読むための束縛だけを残す。他成分の参照は射影の支持ではない。
                let used = read_bindings(env, id, bindings, c)?;
                let (carrier, positions) = implicit_support(env, id, &used, reading, c)?;
                out.push(local_result::geometry::Projection {
                    read,
                    path,
                    field: None,
                    values: vec![value.clone()],
                    support: local_result::geometry::Support {
                        carrier,
                        positions,
                        visible: visible_slots(env, id, &used, reading)?,
                    },
                });
            }
            _ => {}
        }
    }
    Ok(())
}
fn field_path<'a>(env: &'a Environment<'_>, mut id: usize) -> Result<Option<(&'a str, Vec<&'a str>)>, ValidationFailure> {
    let mut fields = vec![];
    loop {
        env.control.clone().checkpoint(Checkpoint::Localize)?;
        match &env.inputs.law().exprs[id].kind {
            ExprKind::Group(child) => id = *child,
            ExprKind::Field { base, name } => {
                fields.push(name.name.as_str());
                id = *base;
            }
            ExprKind::Dotted(parts) if !parts.is_empty() => {
                fields.extend(parts[1..].iter().rev().map(|p| p.name.as_str()));
                fields.reverse();
                return Ok(Some((parts[0].name.as_str(), fields)));
            }
            _ => return Ok(None),
        }
    }
}
fn visible_slots(
    env: &Environment<'_>,
    id: usize,
    bindings: &[(String, Scalar)],
    reading: &str,
) -> Result<Vec<Fact>, ValidationFailure> {
    let mut visible = vec![];
    let mut pending = vec![id];
    while let Some(id) = pending.pop() {
        env.control.clone().checkpoint(Checkpoint::Localize)?;
        let expr = &env.inputs.law().exprs[id];
        match &expr.kind {
            ExprKind::Group(child) => { pending.push(*child); continue; }
            ExprKind::Tuple(items) => { pending.extend(items.iter().rev()); continue; }
            ExprKind::Bool(_) | ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Unit => continue,
            _ => {}
        }
        let (variable, fields) = field_path(env, id)?
            .ok_or_else(|| unsupported(expr.span, "明示localの複合読取りの因子分解は未実装"))?;
        let (_, root) = bindings.iter().find(|(n, _)| n == variable)
            .ok_or_else(|| unsupported(expr.span, "明示localの読取り元が束縛でない"))?;
        let Some((last, prefix)) = fields.split_last() else { continue; };
        let mut owner = known(root.clone());
        for field in prefix {
            env.control.clone().checkpoint(Checkpoint::Localize)?;
            owner = env.scoped_field(owner, field, &Scope::default(), reading, expr.span)?;
        }
        let Some(Scalar::Subject { snapshot, subject, entity }) = &owner.known_value else {
            return Err(unsupported(expr.span, "明示localのfield読取り元が確定した参照でない"));
        };
        visible.push(Fact { snapshot: snapshot.clone(), subject: subject.clone(), field: Some(format!("{entity}.{last}")), atom: None });
    }
    visible.sort();
    visible.dedup();
    Ok(visible)
}
/// 固定状態の参照経路では、中間参照を値座標の公開要件へ混ぜない。
/// let/helper等の一般因子分解はここで推測せず、従来の支持検査へ戻す。
pub(in crate::observed) fn fixed_chain_visibility(
    env: &Environment<'_>, roots: &[usize], bindings: &[(String, Scalar)], reading: &str,
    c: &mut Control,
) -> Result<Option<(Vec<Json>, Vec<Fact>)>, ValidationFailure> {
    let mut pending = roots.to_vec();
    let mut carrier = vec![];
    for (_, value) in bindings { subject_carrier(value, &mut carrier, c)?; }
    let variables = bindings.iter().map(|(n,v)|(n.clone(),known(v.clone()))).collect();
    let mut visible = vec![];
    let mut chain = false;
    while let Some(id) = pending.pop() {
        c.checkpoint(Checkpoint::Localize)?;
        match &env.inputs.law().exprs[id].kind {
            ExprKind::Group(child) | ExprKind::Unary { operand: child, .. } => pending.push(*child),
            ExprKind::Binary { lhs, rhs, .. } => pending.extend([*lhs,*rhs]),
            ExprKind::Tuple(items) => pending.extend(items),
            ExprKind::Bool(_) | ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Unit => {},
            ExprKind::Dotted(_) | ExprKind::Field { .. } => {
                let Some((name, fields)) = field_path(env,id)? else { return Ok(None); };
                if !bindings.iter().any(|(n,_)|n==name) { return Ok(None); }
                chain |= fields.len()>1;
                visible.extend(visible_slots(env,id,bindings,reading)?);
                let value = env.scoped_ast(id,&variables,&Scope::default(),reading)?;
                if value.condition_failed || value.condition_pending { return Ok(None); }
                if let Some(value)=value.known_value { subject_carrier(&value,&mut carrier,c)?; }
            }
            _ => return Ok(None),
        }
    }
    carrier.sort_by_key(Json::canonical); carrier.dedup();
    visible.sort(); visible.dedup();
    Ok(chain.then_some((carrier,visible)))
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
    coordinates: &[NodeRef],
    states: &[Environment<'_>],
    c: &mut Control,
) -> Result<Vec<Context>, ValidationFailure> {
    let Signature::Local { params, .. } = &declaration.signature else {
        return Err("local署名がない".into());
    };
    let mut assignments = vec![vec![]];
    let mut missing = vec![];
    for p in params {
        let values = change_search::domain(env, &p.ty, p.span, &mut missing)?;
        let Some(values) = values else {
            if missing.is_empty() {
                return Err(unsupported(declaration.span, "localのparameter域が未確定"));
            }
            return Ok(vec![Context {
                locals: vec![],
                carrier: vec![],
                positions: vec![],
                visible: vec![],
                read_supports: vec![],
                read_refs: vec![],
                projections: vec![],
                readings: vec![],
                arguments: vec![],
                reasons: vec![Reason {
                    kind: ReasonKind::Missing,
                    request: request.id.clone(),
                    dependencies: coordinates.to_vec(),
                    missing,
                    location: Some(Location::Law {
                        span: declaration.span,
                    }),
                }],
                scope: Scope::default(),
            }]);
        };
        let mut next = vec![];
        for binding in assignments {
            for value in &values {
                c.checkpoint(Checkpoint::Localize)?;
                let mut instance = binding.clone();
                instance.push((p.name.clone(), value.clone()));
                next.push(instance);
            }
        }
        assignments = next;
    }
    let mut contexts = vec![];
    for bindings in &assignments {
        let context = materialize_instance(env, b, declaration, request, bindings, coordinates, states, c)?;
        let stopped = context.reasons.iter().any(|r| matches!(r.kind, ReasonKind::Stop(_)));
        contexts.push(context);
        if stopped { break; }
    }
    Ok(contexts)
}
fn materialize_instance(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    declaration: &Declaration,
    request: &Request,
    bindings: &[(String, Scalar)],
    coordinates: &[NodeRef],
    states: &[Environment<'_>],
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
        visible: vec![],
        read_supports: vec![],
        read_refs: vec![],
        projections: vec![],
        readings: vec![],
        arguments: vec![],
        reasons: vec![],
        scope: Scope::default(),
    };
    let mut checks = owned_call::Checks::default();
    let result = (|| -> Result<(), ValidationFailure> {
    let mut absent = vec![];
    let mut owner_values = BTreeMap::new();
    for (p, (_, v)) in params.iter().zip(bindings) {
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
    for state in states {
        c.checkpoint(Checkpoint::Localize)?;
        let mut varying = owned_call::Checks::default();
        let mut owners = BTreeMap::new();
        for (p, (_, v)) in params.iter().zip(bindings) {
            state.owned_call_value_check(&p.ty, &super::super::term::affine::Value::Known(v.clone()),
                &owners, &declaration.reading, declaration.span, &mut varying)?;
            owners.insert(p.name.as_str(), Some(v));
        }
        if varying.failure.is_some() != checks.failure.is_some()
            || varying.blocked != checks.blocked || varying.missing != checks.missing {
            return Err(unsupported(declaration.span, "自由状態で所属が変わるlocalは未実装"));
        }
        out.scope.merge(&varying.scope);
    }
    out.scope.merge(&checks.scope);
    out.positions.extend(positions(&checks.support));
    if checks.failure.is_some() {
        return Ok(());
    }
    absent.extend(checks.missing.iter().cloned());
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
        return Ok(());
    }
    let variables = bindings
        .iter()
        .map(|(n, v)| (n.clone(), known(v.clone())))
        .collect();
    let node_bindings = bindings
        .iter()
        .map(|(n, v)| Ok((n.clone(), change_result::value(b, v)?)))
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    for (_, v) in bindings {
        subject_carrier(v, &mut out.carrier, c)?;
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
        let mut guard_missing = absent.clone();
        let consistent = (|| -> Result<(), ValidationFailure> {
            for state in states {
                c.checkpoint(Checkpoint::Localize)?;
                let (other, _, other_absent) = evaluate_read(state, *id, &variables, &scope, &declaration.reading)?;
                guard_missing.extend(other_absent.iter().cloned());
                if other.known_value != value.known_value || other.condition_failed != value.condition_failed
                    || other.condition_pending != value.condition_pending || other_absent != absent {
                    return Err(unsupported(declaration.span, "自由状態で適用条件が変わるlocalは未実装"));
                }
            }
            Ok(())
        })();
        if let Err(error) = consistent {
            if !guard_missing.is_empty() {
                guard_missing.sort();
                guard_missing.dedup();
                reason(&mut out, request, ReasonKind::Missing, guard_missing,
                    declaration.span, vec![expression]);
            }
            return Err(error);
        }
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
            return Ok(());
        }
        if value.known_value == Some(Scalar::Bool(false)) {
            return Ok(());
        }
        if value.known_value != Some(Scalar::Bool(true)) {
            return Err("local guardがBoolでない".into());
        }
    }
    let states = if states.is_empty() { vec![env] } else { states.iter().collect() };
    for id in reads {
        c.checkpoint(Checkpoint::Localize)?;
        let expression = change_result::source_expression(b, env, *id, &node_bindings, &[])?;
        out.arguments.push(expression);
        let mut values = vec![];
        let mut carrier = vec![];
        let mut dependencies = vec![];
        let mut visible = vec![];
        let mut missing_reason: Option<usize> = None;
        let mut projected = vec![];
        for state in &states {
            c.checkpoint(Checkpoint::Localize)?;
            let (read, positions, missing) =
                evaluate_read(state, *id, &variables, &scope, &declaration.reading)?;
            b.parts[expression.0 - b.base].scope.merge(&read.scope);
            out.scope.merge(&read.scope);
            dependencies.extend(positions);
            if !missing.is_empty() {
                let index = if let Some(index) = missing_reason { index } else {
                    let index = out.reasons.len();
                    reason(&mut out, request, ReasonKind::Missing, vec![],
                        declaration.span, vec![expression]);
                    missing_reason = Some(index);
                    index
                };
                out.reasons[index].missing.extend(missing);
                out.reasons[index].missing.sort();
                out.reasons[index].missing.dedup();
            }
            if read.condition_failed {
                return Err(unsupported(declaration.span, "local読取りの式の適用条件が不成立"));
            }
            if read.condition_pending || read.known_value.is_none() {
                if missing_reason.is_none() {
                    return Err(unsupported(declaration.span, "localの読取り値が未確定"));
                }
                continue;
            }
            let state_visible = visible_slots(state, *id, bindings, &declaration.reading)?;
            // changeは参照fieldを更新しない。fieldだけの経路の末端位置は各状態で同じ。
            visible = state_visible;
            let value = read.known_value.ok_or("localの確定値がない")?;
            subject_carrier(&value, &mut carrier, c)?;
            projections(state, *id, &value, out.readings.len(), bindings,
                &declaration.reading, &mut projected, c)?;
            if !values.contains(&value) { values.push(value); }
        }
        out.positions.extend(dependencies.iter().cloned());
        out.visible.extend(visible.iter().cloned());
        if missing_reason.is_some() { continue; }
        let ty = values.first().ok_or("localの読取り像が空")?.ty();
        let actual = values.iter().map(|v| change_result::value(b, v)).collect::<Result<Vec<_>, _>>()?;
        let image = local_result::domain(b, &ty, &actual)?;
        for projection in projected {
            if let Some(existing) = out.projections.iter_mut().find(|p| p.read == projection.read && p.path == projection.path) {
                existing.support.carrier.extend(projection.support.carrier);
                existing.support.positions.extend(projection.support.positions);
                existing.support.visible.extend(projection.support.visible);
                for value in projection.values {
                    if !existing.values.contains(&value) { existing.values.push(value); }
                }
            } else { out.projections.push(projection); }
        }
        out.readings.push(Json::obj([
            ("expression", expression.wire()), ("type", ty.wire()), ("domain", image.wire()),
        ]));
        out.arguments.push(image);
        out.read_refs.extend([expression, image]);
        out.carrier.extend(carrier.iter().cloned());
        for (_, v) in &read_bindings(env, *id, bindings, c)? {
            subject_carrier(v, &mut carrier, c)?;
        }
        carrier.sort_by_key(Json::canonical); carrier.dedup();
        let mut dependencies = positions(&dependencies).collect::<Vec<_>>();
        dependencies.sort(); dependencies.dedup();
        visible.sort(); visible.dedup();
        out.read_supports.push(local_result::geometry::Support { carrier, positions: dependencies, visible });
    }
    for projection in &mut out.projections {
        projection.support.carrier.sort_by_key(Json::canonical); projection.support.carrier.dedup();
        projection.support.positions.sort(); projection.support.positions.dedup();
        projection.support.visible.sort(); projection.support.visible.dedup();
    }
    out.carrier.sort_by_key(Json::canonical);
    out.carrier.dedup();
    out.positions.sort();
    out.positions.dedup();
    out.positions = positions(&out.positions).collect();
    out.positions.sort();
    out.positions.dedup();
    out.visible.sort();
    out.visible.dedup();
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
    Ok(())
    })();
    if let Err(error) = result {
        out.scope.merge(&checks.scope);
        out.positions.extend(positions(&checks.support));
        if checks.failure.is_none() && !checks.missing.is_empty() {
            reason(&mut out, request, ReasonKind::Missing, checks.missing,
                declaration.span, coordinates.to_vec());
        }
        let (kind, location) = match error {
            ValidationFailure::Stop(stop) => (ReasonKind::Stop(stop), None),
            ValidationFailure::UnsupportedExpression { location, .. } => {
                let mut types = vec![];
                for r in &out.arguments {
                    if let Some(part) = r.0.checked_sub(b.base).and_then(|i| b.parts.get(i)) {
                        if let NodeType::Expression(ty) = &part.ty {
                            if !types.contains(ty) { types.push(ty.clone()); }
                        }
                    }
                }
                (ReasonKind::UnsupportedAlgorithm { question: QuestionKind::Localize,
                    operand_types: types, method: "local_reading".into() }, Some(location))
            }
            other => return Err(other),
        };
        out.reasons.push(Reason { kind, request: request.id.clone(),
            dependencies: coordinates.iter().chain(&out.arguments).copied().collect(),
            missing: vec![], location });
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::{control::{Limits, Usage}, input::check_inputs, request::resolve_native_for_test};
    #[allow(dead_code)]
    mod fixture {
        use crate as archsig;
        include!("../../tests/common/architecture_environment.rs");
    }
    fn quiet() -> Control { Control::new(Limits::default(), |_| Usage::default()) }
    #[test]
    fn local_owner_missing_survives_the_first_free_state_stop() {
        let map = fixture::remove_atom("p-owner");
        let inputs = check_inputs(fixture::input("local here(a:System,s:State[a]) reads s.free;", Some(&map)), &mut quiet()).unwrap();
        let requests = resolve_native_for_test(inputs.law(), inputs.archmap(), &["c=check(Reservations.roots,x=@v/A)"], &mut quiet()).unwrap();
        let env = Environment::with_requests(&inputs, requests.requests(), &mut quiet()).unwrap();
        let declaration = &inputs.law().declarations["Reservations.here"];
        let bindings = vec![
            ("a".into(), Scalar::Subject { snapshot:"v".into(), subject:"A".into(), entity:"Reservations.System".into() }),
            ("s".into(), Scalar::Subject { snapshot:"v".into(), subject:"p".into(), entity:"Reservations.State".into() }),
        ];
        for mode in 0..3 {
            let state = Environment::with_requests(&inputs, requests.requests(), &mut quiet()).unwrap();
            let graph = Graph::new(&quiet());
            let mut b = Builder { g:&graph, base:0, parts:vec![] };
            let mut c = Control::new(Limits { time_ms:Some(1), memory_mib:Some(1) }, move |point| {
                if point != Checkpoint::Localize { return Usage::default(); }
                match mode {
                    0 => Usage { elapsed_ms:2, ..Usage::default() },
                    1 => Usage { memory_mib:2, ..Usage::default() },
                    _ => Usage { signal:Some(crate::result::Signal::Term), ..Usage::default() },
                }
            });
            let context = materialize_instance(&env, &mut b, declaration, &requests.requests()[0], &bindings, &[], &[state], &mut c).unwrap();
            assert!(context.reasons.iter().any(|r| matches!(r.kind, ReasonKind::Stop(_))));
            assert!(context.reasons.iter().any(|r| r.missing.iter().any(|f| f.subject=="p" && f.field.as_deref()==Some("Reservations.State.owner"))));
        }
    }
}
