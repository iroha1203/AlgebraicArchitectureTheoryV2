//! 有限changeの全自由状態と許可作用の像を分け、Law支持ごとの状態を得る。
use super::*;
use crate::observed::environment::change_evaluation::{self, Candidates, State};

pub(super) struct Reading {
    pub expression: usize,
    pub bindings: Vec<(String, Scalar)>,
    pub support: geometry::Support,
    pub values: Vec<Scalar>,
}
pub(super) struct Model {
    pub change: String,
    pub candidates: Candidates,
    pub bindings: Vec<(String, Scalar)>,
    pub slots: Vec<Fact>,
    pub slot_types: Vec<Type>,
    pub points: Vec<Vec<Scalar>>,
    pub candidate_points: Vec<Option<usize>>,
    pub requirements: Vec<(String, Vec<(String, Scalar)>)>,
    pub universal: Vec<(String, crate::law::model::Param, Vec<Scalar>)>,
    pub truth: Vec<Vec<bool>>,
    pub law_supports: Vec<geometry::Support>,
    pub readings: Vec<Reading>,
    pub missing: Vec<Fact>,
    pub scope: Scope,
}
fn empty_support() -> geometry::Support {
    geometry::Support {
        carrier: vec![],
        positions: vec![],
        visible: vec![],
    }
}
fn add_subject(
    support: &mut geometry::Support,
    value: &Scalar,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        match value {
            Scalar::Subject { .. } => support.carrier.push(Json::obj([
                ("type", value.ty().wire()),
                ("value", value.wire()),
            ])),
            Scalar::Tuple(values) => pending.extend(values),
            _ => {}
        }
    }
    Ok(())
}
fn normalize(support: &mut geometry::Support) {
    support.carrier.sort_by_key(Json::canonical);
    support.carrier.dedup();
    support.positions.sort();
    support.positions.dedup();
    support.visible = support.positions.clone();
}
pub(super) fn analyze(
    original: &Environment<'_>,
    env: &Environment<'_>,
    g: &Graph,
    witness: &ArchitectureWitness,
    request: &Request,
    c: &mut Control,
) -> Result<(Option<Model>, Vec<Fact>), ValidationFailure> {
    let reading = witness.construction().reading();
    let explicit = env.inputs.law().declarations.values().any(|d|
        d.reading == reading && matches!(d.signature, Signature::Local { .. }));
    let change_name = request
        .arguments
        .iter()
        .find_map(|a| match (&*a.name, &a.value) {
            ("using", Selector::Declaration { name }) => Some(name),
            _ => None,
        })
        .ok_or("局所系のchange名がない")?;
    let change = &env.inputs.law().declarations[change_name];
    let Signature::Change { params, .. } = &change.signature else {
        return Err("局所changeの署名がない".into());
    };
    if change.reading != reading {
        return Err(unsupported("局所changeと対象readingが異なる"));
    }
    let mut fixed =
        Environment::try_primitive_valuation(env.inputs, &env.architecture_values(), c)?
            .ok_or("局所対象の値が不適合")?;
    fixed.select_local_object(witness, c)?;
    let mut missing = vec![];
    let first = params.first().ok_or("changeの対象parameterがない")?;
    let subjects = change_search::domain(&fixed, &first.ty, first.span, &mut missing)?;
    if !missing.is_empty() {
        return Ok((None, missing));
    }
    if subjects.is_none() {
        return Err(unsupported("有限changeの対象域が未確定"));
    }
    let mut subjects = subjects.ok_or("changeの対象域がない")?;
    let construction = witness.construction();
    subjects.retain(|v| match v {
        Scalar::Subject {
            snapshot, subject, ..
        } => std::iter::once(construction.root())
            .chain(construction.local_domain().known())
            .any(|f| f.snapshot == *snapshot && f.subject == *subject),
        _ => false,
    });
    let candidates =
        change_evaluation::candidates(&fixed, change, &subjects).map_err(|e| e.cause)?;
    let fields = change_evaluation::update_fields(&fixed, change)?;
    let mut slots = vec![];
    for subject in &subjects {
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = subject
        else {
            return Err("更新対象が参照でない".into());
        };
        for field in &fields {
            slots.push(Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: Some(format!("{entity}.{field}")),
                atom: None,
            });
        }
    }
    slots.sort();
    slots.dedup();
    let mut slot_types = vec![];
    let mut points = vec![vec![]];
    for slot in &slots {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let ty = fixed
            .field(
                &slot.snapshot,
                &slot.subject,
                slot.field.as_ref().ok_or("更新fieldがない")?,
            )?
            .ty
            .erase();
        let values = change_search::domain(&fixed, &ty, change.span, &mut missing)?;
        if !missing.is_empty() {
            return Ok((None, missing));
        }
        let values = values.ok_or_else(|| unsupported("自由状態の有限域が未確定"))?;
        let mut next = vec![];
        for prefix in points {
            for value in &values {
                c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
                let mut point = prefix.clone();
                point.push(value.clone());
                next.push(point);
            }
        }
        points = next;
        slot_types.push(ty);
    }
    let bindings = request
        .arguments
        .iter()
        .filter_map(|a| a.name.strip_prefix("bind.").map(|name| (name, a)))
        .map(|(name, a)| Ok((name.to_owned(), change_search::selector(original, g, &a.value)?)))
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    let selected = request.declaration();
    let mut requirements = vec![];
    let mut universal = vec![];
    for law in env.inputs.law().declarations.values().filter(|d| {
        d.reading == reading
            && match selected {
                Some(name) => d.name == name,
                None => matches!(
                    d.signature,
                    Signature::Law {
                        role: crate::law::ast::Role::Required,
                        ..
                    }
                ),
            }
    }) {
        let Signature::Law { params, .. } = &law.signature else {
            return Err("局所Lawの署名がない".into());
        };
        let mut rows = vec![vec![]];
        for p in params {
            let values = if let Some(arg) = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
            {
                vec![change_search::selector(original, g, &arg.value)?]
            } else {
                let values = change_search::domain(&fixed, &p.ty, p.span, &mut missing)?;
                if !missing.is_empty() {
                    return Ok((None, missing));
                }
                let values = values.ok_or_else(|| unsupported("局所Lawのparameter域が未確定"))?;
                universal.push((law.name.clone(), p.clone(), values.clone()));
                values
            };
            let mut next = vec![];
            for row in rows {
                for value in &values {
                    c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
                    let mut row = row.clone();
                    row.push((p.name.clone(), value.clone()));
                    next.push(row);
                }
            }
            rows = next;
        }
        requirements.extend(rows.into_iter().map(|row| (law.name.clone(), row)));
    }
    if requirements.is_empty() {
        return Err(unsupported("空のLaw族の有限change局所系は未実装"));
    }
    let mut candidate_points = vec![];
    for candidate in &candidates.rows {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        match candidate.update.state {
            State::Excluded => candidate_points.push(None),
            State::Ready => {
                if candidate
                    .update
                    .values
                    .iter()
                    .map(|(f, _)| f)
                    .ne(slots.iter())
                {
                    return Err(unsupported(
                        "分岐で更新位置が異なる有限change局所系は未実装",
                    ));
                }
                let point = candidate
                    .update
                    .values
                    .iter()
                    .map(|(_, v)| v.clone())
                    .collect::<Vec<_>>();
                candidate_points.push(Some(
                    points
                        .iter()
                        .position(|p| *p == point)
                        .ok_or("許可作用の像が全自由状態にない")?,
                ));
            }
            State::Undetermined => {
                missing.extend(candidate.update.missing.iter().cloned());
                candidate_points.push(None);
            }
            State::ConditionFailed => return Err(unsupported("局所changeの式の適用条件が不成立")),
        }
    }
    if candidates
        .rows
        .iter()
        .any(|r| r.update.state == State::Undetermined)
        && missing.is_empty()
    {
        return Err(unsupported("有限changeの適用条件が未確定"));
    }
    let mut law_supports = vec![empty_support(); requirements.len()];
    let mut truth = vec![];
    let mut readings: Vec<Reading> = vec![];
    let mut scope = Scope::default();
    for point in &points {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let mut assignments = env
            .architecture_values()
            .into_iter()
            .collect::<BTreeMap<_, _>>();
        assignments.extend(slots.iter().cloned().zip(point.iter().cloned()));
        let mut state = Environment::try_primitive_valuation(
            env.inputs,
            &assignments.into_iter().collect::<Vec<_>>(),
            c,
        )?
        .ok_or_else(|| unsupported("自由状態の参照・所属条件が不適合"))?;
        state.select_local_object(witness, c)?;
        let mut row_truth = vec![];
        for (i, (name, bindings)) in requirements.iter().enumerate() {
            let law = &env.inputs.law().declarations[name];
            let (row, absent, evaluated) = state.local_point(law, bindings)?;
            missing.extend(absent);
            missing.extend(row.application_missing.iter().cloned());
            scope.merge(&row.scope);
            let holds = if row.application == Some(false) {
                true
            } else if row.application != Some(true) || row.condition_pending {
                if missing.is_empty() {
                    return Err(unsupported("有限局所Lawの適用条件が未確定"));
                }
                false
            } else if row.condition_failed {
                false
            } else {
                match (row.guard, row.predicate) {
                    (Some(false), _) | (Some(true), Some(true)) => true,
                    (Some(true), Some(false)) => false,
                    _ => {
                        if missing.is_empty() {
                            return Err(unsupported("有限局所Lawの値が未確定"));
                        }
                        false
                    }
                }
            };
            row_truth.push(holds);
            // 短絡で値が確定しても、固定位置の欠測は読取りを完成させない。
            // 各点の欠測収集は続け、公開構成はMissingとして返す。
            if !missing.is_empty() {
                continue;
            }
            let support = &mut law_supports[i];
            for (_, value) in bindings {
                add_subject(support, value, c)?;
            }
            for fact in row.support.iter().filter(|f| f.field.is_some()) {
                let subject = env.subject(&fact.snapshot, &fact.subject)?;
                add_subject(
                    support,
                    &Scalar::Subject {
                        snapshot: fact.snapshot.clone(),
                        subject: fact.subject.clone(),
                        entity: subject.ty.clone(),
                    },
                    c,
                )?;
                support.positions.push(Fact {
                    atom: None,
                    ..fact.clone()
                });
            }
            if explicit { continue; }
            let Signature::Law { body, guard, .. } = law.signature else {
                return Err("局所Lawの署名がない".into());
            };
            let roots = match env.inputs.law().exprs[body].kind {
                ExprKind::Binary {
                    op: BinOp::Eq,
                    lhs,
                    rhs,
                } => vec![lhs, rhs],
                _ => vec![body],
            };
            for read in evaluated.into_iter().filter(|n| {
                roots.contains(&n.expression)
                    || guard == Some(n.expression)
                    || match &env.inputs.law().exprs[n.expression].kind {
                        ExprKind::Field { .. } => true,
                        ExprKind::Dotted(parts) => {
                            parts.len() > 1
                                && n.bindings.iter().any(|(name, _)| *name == parts[0].name)
                        }
                        _ => false,
                    }
            }) {
                let Some(value) = read.value else { continue };
                let bindings = super::super::environment::local_read::read_bindings(
                    &state, read.expression, &read.bindings, c,
                )?;
                let (carrier, positions) = super::super::environment::local_read::implicit_support(
                    &state,
                    read.expression,
                    &bindings,
                    reading,
                    c,
                )?;
                let at = readings
                    .iter()
                    .position(|r| r.expression == read.expression && r.bindings == bindings);
                let r = if let Some(at) = at {
                    &mut readings[at]
                } else {
                    readings.push(Reading {
                        expression: read.expression,
                        bindings,
                        support: empty_support(),
                        values: vec![],
                    });
                    readings.last_mut().ok_or("読取りの追加失敗")?
                };
                r.support.carrier.extend(carrier);
                r.support.positions.extend(positions);
                if !r.values.contains(&value) {
                    r.values.push(value);
                }
            }
        }
        truth.push(row_truth);
    }
    for support in &mut law_supports {
        normalize(support);
    }
    for read in &mut readings {
        normalize(&mut read.support);
    }
    missing.sort();
    missing.dedup();
    Ok((
        Some(Model {
            bindings,
            change: change_name.clone(),
            candidates,
            slots,
            slot_types,
            points,
            candidate_points,
            requirements,
            universal,
            truth,
            law_supports,
            readings,
            missing,
            scope,
        }),
        vec![],
    ))
}
