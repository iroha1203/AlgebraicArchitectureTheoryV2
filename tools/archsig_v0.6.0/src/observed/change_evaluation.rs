//! 元changeの束縛と同時更新。右辺はすべて変更前の同じ環境で評価する。
use super::*;
use crate::law::model::{Declaration, Signature};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum State {
    Ready,
    Excluded,
    Undetermined,
    ConditionFailed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Update {
    pub state: State,
    pub values: Vec<(Fact, Scalar)>,
    pub missing: Vec<Fact>,
    pub support: Vec<Fact>,
    pub scope: Scope,
}

fn known(value: Scalar) -> SourceValue {
    SourceValue {
        condition_failed: false,
        condition_pending: false,
        symbolic: None,
        comparison: None,
        affine: None,
        scope: Scope::default(),
        known_value: Some(value),
        support: vec![],
        scalar_scope: Some(Scope::default()),
    }
}

impl Update {
    fn retain(&mut self, value: &SourceValue) {
        self.support.extend(value.support.iter().cloned());
        self.scope.merge(&value.scope);
        if value.condition_failed {
            self.state = State::ConditionFailed;
        } else if (value.condition_pending || value.known_value.is_none())
            && self.state != State::ConditionFailed
        {
            self.state = State::Undetermined;
        }
    }
}

/// 呼出し元が選んだ一つの元Assignmentを評価する。値の供給でguardを代替しない。
pub(in crate::observed) fn evaluate(
    environment: &Environment<'_>,
    declaration: &Declaration,
    bindings: &[(String, Scalar)],
) -> Result<Update, ValidationFailure> {
    evaluate_on_fields(environment, declaration, bindings, &[])
}

/// Read the simultaneous result on the caller's comparison coordinates.
/// A coordinate omitted by the change keeps its value before the update.
pub(in crate::observed) fn evaluate_on_fields(
    environment: &Environment<'_>,
    declaration: &Declaration,
    bindings: &[(String, Scalar)],
    fields: &[String],
) -> Result<Update, ValidationFailure> {
    let outer = environment
        .missing_slot_reads
        .replace(Some(BTreeSet::new()));
    let result = evaluate_inner(environment, declaration, bindings, fields);
    let missing = environment
        .missing_slot_reads
        .replace(outer)
        .ok_or("changeの不足位置収集がない")?;
    if let Some(reads) = environment.missing_slot_reads.borrow_mut().as_mut() {
        reads.extend(missing.iter().cloned());
    }
    let mut result = result?;
    if result.state == State::Undetermined {
        result.missing.extend(missing.into_iter().filter(|f| {
            !environment
                .primitive_valuation
                .as_ref()
                .is_some_and(|v| v.contains_key(f))
        }));
        result.missing.sort();
        result.missing.dedup();
    }
    result.support.sort();
    result.support.dedup();
    Ok(result)
}
fn evaluate_inner(
    environment: &Environment<'_>,
    declaration: &Declaration,
    bindings: &[(String, Scalar)],
    fields: &[String],
) -> Result<Update, ValidationFailure> {
    environment.tick()?;
    let Signature::Change {
        params,
        guard,
        body,
    } = &declaration.signature
    else {
        return Err("更新の元宣言がchangeでない".into());
    };
    if params.len() != bindings.len() || params.is_empty() {
        return Err("changeの元parameter数が違う".into());
    }
    let mut vars = BTreeMap::new();
    let mut checked = BTreeMap::new();
    let mut checks = owned_call::Checks::default();
    for (parameter, (name, value)) in params.iter().zip(bindings) {
        environment.tick()?;
        if parameter.name != *name || parameter.ty.erase() != value.ty() {
            return Err("changeの元parameter名または型が違う".into());
        }
        data::check(value, environment.inputs.law(), &environment.control)?;
        environment.owned_call_value_check(
            &parameter.ty,
            &super::super::term::affine::Value::Known(value.clone()),
            &checked,
            &declaration.reading,
            declaration.span,
            &mut checks,
        )?;
        checked.insert(name.as_str(), Some(value));
        vars.insert(name.clone(), known(value.clone()));
    }
    let mut result = Update {
        state: if checks.failure.is_some() {
            State::Excluded
        } else if checks.blocked {
            State::Undetermined
        } else {
            State::Ready
        },
        values: vec![],
        support: checks.support,
        scope: checks.scope.clone(),
        missing: checks.missing,
    };
    let mut base = checks.scope;
    base.readings.insert(declaration.reading.clone());
    if result.state != State::Ready {
        return Ok(result);
    }
    if let Some(guard) = guard {
        let value = environment.scoped_ast(*guard, &vars, &base, &declaration.reading)?;
        result.retain(&value);
        if result.state != State::Ready {
            return Ok(result);
        }
        match value.known_value {
            Some(Scalar::Bool(false)) => {
                result.state = State::Excluded;
                return Ok(result);
            }
            Some(Scalar::Bool(true)) => {}
            _ => return Err("change guardの型がBoolでない".into()),
        }
    }
    let mut current = *body;
    loop {
        environment
            .control
            .clone()
            .checkpoint(Checkpoint::PrimitiveValuation)?;
        match &environment.inputs.law().exprs[current].kind {
            ExprKind::Group(inner) => current = *inner,
            ExprKind::Let { name, value, body } => {
                let value = environment.scoped_ast(*value, &vars, &base, &declaration.reading)?;
                // 未使用の値そのものは強制しないが、式の適合条件は通常letと同じく残す。
                if value.condition_failed || value.condition_pending {
                    result.retain(&value);
                    break;
                }
                vars.insert(name.name.clone(), value);
                current = *body;
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let condition =
                    environment.scoped_ast(*cond, &vars, &base, &declaration.reading)?;
                result.retain(&condition);
                if result.state != State::Ready {
                    break;
                }
                current = match condition.known_value {
                    Some(Scalar::Bool(true)) => *then_branch,
                    Some(Scalar::Bool(false)) => *else_branch,
                    _ => return Err("changeの分岐条件がBoolでない".into()),
                };
            }
            ExprKind::With {
                base: target,
                updates,
            } => {
                let target = environment.scoped_ast(*target, &vars, &base, &declaration.reading)?;
                result.retain(&target);
                let Some(Scalar::Subject {
                    snapshot,
                    subject,
                    entity,
                }) = &target.known_value
                else {
                    if result.state == State::Ready {
                        return Err("changeの更新先がsubjectでない".into());
                    }
                    break;
                };
                for (field, expression) in updates {
                    environment.tick()?;
                    let value =
                        environment.scoped_ast(*expression, &vars, &base, &declaration.reading)?;
                    result.retain(&value);
                    if let Some(value) = value.known_value {
                        result.values.push((
                            Fact {
                                snapshot: snapshot.clone(),
                                subject: subject.clone(),
                                field: Some(format!("{entity}.{}", field.name)),
                                atom: None,
                            },
                            value,
                        ));
                    }
                }
                for name in fields {
                    environment.tick()?;
                    if updates.iter().any(|(field, _)| field.name == *name) {
                        continue;
                    }
                    let value = environment.scoped_field(
                        target.clone(), name, &base, &declaration.reading, declaration.span,
                    )?;
                    result.retain(&value);
                    if let Some(value) = value.known_value {
                        result.values.push((Fact {
                            snapshot: snapshot.clone(), subject: subject.clone(),
                            field: Some(format!("{entity}.{name}")), atom: None,
                        }, value));
                    }
                }
                break;
            }
            _ => return Err("検査済みchangeの結果がwith更新でない".into()),
        }
    }
    result.values.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(result)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Candidate {
    /// 元change parameterをinstance順・宣言順に保持する。更新状態で同一視しない。
    pub parameters: Vec<Scalar>,
    pub update: Update,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Candidates {
    pub subjects: Vec<Scalar>,
    pub parameter_types: Vec<Type>,
    pub rows: Vec<Candidate>,
    pub complete: bool,
}

/// 全guardが偽でも、更新座標の型を空の状態型へ変えない。
pub(in crate::observed) fn update_fields(
    environment: &Environment<'_>,
    declaration: &Declaration,
) -> Result<Vec<String>, ValidationFailure> {
    update_shape(environment, declaration).map(|(_, fields)| fields)
}
/// 元withの実base出現と、既存状態表の共通更新座標を返す。式評価は行わない。
pub(in crate::observed) fn update_shape(
    environment: &Environment<'_>,
    declaration: &Declaration,
) -> Result<(usize, Vec<String>), ValidationFailure> {
    let Signature::Change { body, .. } = &declaration.signature else {
        return Err("更新座標の宣言がchangeでない".into());
    };
    let mut pending = vec![*body];
    let mut fields: Option<Vec<String>> = None;
    let mut base = None;
    while let Some(id) = pending.pop() {
        environment.tick()?;
        match &environment.inputs.law().exprs[id].kind {
            ExprKind::Group(inner) => pending.push(*inner),
            ExprKind::Let { body, .. } => pending.push(*body),
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => pending.extend([*then_branch, *else_branch]),
            ExprKind::With {
                base: target,
                updates,
            } => {
                base.get_or_insert(*target);
                let mut names = updates
                    .iter()
                    .map(|(f, _)| f.name.clone())
                    .collect::<Vec<_>>();
                names.sort();
                if fields.as_ref().is_some_and(|prior| prior != &names) {
                    return Err(ValidationFailure::UnsupportedExpression {
                        location: Location::Law {
                            span: declaration.span,
                        },
                        feature: "state tables for changes with different update slot sets across branches are not implemented".into(),
                    });
                }
                fields = Some(names);
            }
            _ => return Err("検査済みchangeの更新座標がない".into()),
        }
    }
    Ok((
        base.ok_or("changeの更新先出現がない")?,
        fields.ok_or("changeの更新座標がない")?,
    ))
}

#[derive(Debug)]
pub(in crate::observed) struct CandidateFailure {
    pub cause: ValidationFailure,
    pub partial: Candidates,
}

/// 指定された全instanceの元parameter直積を列挙し、同時更新を作る。
/// instanceの選択は元Architectureから行い、ここでは重複・型不適合を拒否する。
pub(in crate::observed) fn candidates(
    environment: &Environment<'_>,
    declaration: &Declaration,
    subjects: &[Scalar],
) -> Result<Candidates, CandidateFailure> {
    let mut result = Candidates {
        subjects: subjects.to_vec(),
        parameter_types: vec![],
        rows: vec![],
        complete: false,
    };
    let computed = (|| -> Result<(), ValidationFailure> {
        let Signature::Change { params, .. } = &declaration.signature else {
            return Err("候補域の元宣言がchangeでない".into());
        };
        let first = params.first().ok_or("changeの第一parameterがない")?;
        let mut seen = BTreeSet::new();
        for subject in subjects {
            environment.tick()?;
            let Scalar::Subject {
                snapshot,
                subject: name,
                ..
            } = subject
            else {
                return Err("change instanceがsubjectでない".into());
            };
            if subject.ty() != first.ty.erase() || !seen.insert((snapshot, name)) {
                return Err("change instanceの型が違うか重複している".into());
            }
            for parameter in params.iter().skip(1) {
                if !super::super::finite::completion_supported(
                    &parameter.ty,
                    environment.inputs.law(),
                    &environment.control,
                )? {
                    return Err(ValidationFailure::UnsupportedExpression {
                        location: Location::Law {
                            span: parameter.span,
                        },
                        feature: "change parameterの有限全域列挙以外は未実装".into(),
                    });
                }
                result.parameter_types.push(parameter.ty.clone());
            }
        }
        let domain = super::super::finite::values(
            &Type::Tuple(result.parameter_types.clone()),
            environment.inputs.law(),
            &environment.control,
            &mut |_| Err("change値parameterに参照域がある".into()),
            &mut |_| {},
        )?;
        for point in domain.values {
            environment.control.clone().checkpoint(Checkpoint::PrimitiveValuation)?;
            let Scalar::Tuple(parameters) = &point else {
                return Err("change parameterの直積がTupleでない".into());
            };
            result.rows.push(candidate(environment,declaration,subjects,&parameters)?);
        }
        result.complete = true;
        Ok(())
    })();
    match computed {
        Ok(()) => Ok(result),
        Err(cause) => Err(CandidateFailure {
            cause,
            partial: result,
        }),
    }
}

/// 一つの元parameter点を全instanceへ同時代入する。全域の算法と再代入で共用する。
pub(in crate::observed) fn candidate(
    environment: &Environment<'_>, declaration: &Declaration,
    subjects: &[Scalar], parameters: &[Scalar],
) -> Result<Candidate, ValidationFailure> {
    let Signature::Change { params, .. } = &declaration.signature else {
        return Err("候補の元宣言がchangeでない".into());
    };
    let first=params.first().ok_or("changeの第一parameterがない")?;
    if parameters.len()!=subjects.len()*(params.len()-1) {
        return Err("元parameter点の次元が違う".into());
    }
            let mut update = Update {
                state: State::Ready,
                values: vec![],
                missing: vec![],
                support: vec![],
                scope: Scope::default(),
            };
            let mut values = BTreeMap::<Fact, Scalar>::new();
            for (index, subject) in subjects.iter().enumerate() {
                let start = index * (params.len() - 1);
                let bindings = std::iter::once((first.name.clone(), subject.clone()))
                    .chain(
                        params
                            .iter()
                            .skip(1)
                            .zip(&parameters[start..start + params.len() - 1])
                            .map(|(p, v)| (p.name.clone(), v.clone())),
                    )
                    .collect::<Vec<_>>();
                let item = evaluate(environment, declaration, &bindings)?;
                update.support.extend(item.support.iter().cloned());
                update.scope.merge(&item.scope);
                update.missing.extend(item.missing);
                update.state = match (&update.state, &item.state) {
                    (State::ConditionFailed, _) | (_, State::ConditionFailed) => {
                        State::ConditionFailed
                    }
                    (State::Excluded, _) | (_, State::Excluded) => State::Excluded,
                    (State::Undetermined, _) | (_, State::Undetermined) => State::Undetermined,
                    _ => State::Ready,
                };
                for (position, value) in item.values {
                    if let Some(previous) = values.get(&position) {
                        if !data::equal(previous, &value, &environment.control)? {
                            update.state = State::ConditionFailed;
                        }
                    } else {
                        values.insert(position, value);
                    }
                }
            }
            update.values = values.into_iter().collect();
            update.missing.sort();
            update.missing.dedup();
    Ok(Candidate { parameters: parameters.to_vec(), update })
}

#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct SolutionRow {
    pub candidate: usize,
    pub member: Option<bool>,
}

/// 元parameter点を、同時更新後の全Law instanceに再代入する。
pub(in crate::observed) fn solution_row(
    environment: &Environment<'_>,
    candidate: &Candidate,
    point: usize,
    requirements: &[(String, Vec<(String, Scalar)>)],
) -> Result<SolutionRow, ValidationFailure> {
    let mut row = SolutionRow {
        candidate: point,
        member: None,
    };
    match candidate.update.state {
        State::Excluded | State::ConditionFailed => {
            row.member = Some(false);
            return Ok(row);
        }
        State::Undetermined => return Ok(row),
        State::Ready => {}
    }
    let mut assignments = environment.primitive_valuation.clone().unwrap_or_default();
    assignments.extend(candidate.update.values.iter().cloned());
    let assignments = assignments.into_iter().collect::<Vec<_>>();
    let Some(mut updated) = Environment::try_primitive_valuation(
        environment.inputs,
        &assignments,
        &mut environment.control.clone(),
    )?
    else {
        row.member = Some(false);
        return Ok(row);
    };
    updated.object = environment.object_domain();
    let mut member = Some(true);
    for (name, bindings) in requirements {
        environment
            .control
            .clone()
            .checkpoint(Checkpoint::PrimitiveValuation)?;
        let declaration = environment
            .inputs
            .law()
            .declarations
            .get(name)
            .ok_or("候補の元Lawがない")?;
        let law = finite_law_valuations::evaluate_change_point(&updated, declaration, bindings, point)?;
        let holds = if law.application == Some(false) {
            Some(true)
        } else if law.application.is_none() || law.condition_pending {
            None
        } else if law.condition_failed {
            Some(false)
        } else {
            match (law.guard, law.predicate) {
                (Some(false), _) | (Some(true), Some(true)) => Some(true),
                (Some(true), Some(false)) => Some(false),
                _ => None,
            }
        };
        member = match (member, holds) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        };
    }
    row.member = member;
    Ok(row)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::control::{Limits, Usage};
    #[allow(dead_code)]
    mod fixture {
        include!("../../tests/common/primitive_valuation_data.rs");
    }
    fn quiet() -> Control {
        Control::new(Limits::default(), |_| Usage::default())
    }
    fn bindings() -> Vec<(String, Scalar)> {
        vec![(
            "c".into(),
            Scalar::Subject {
                snapshot: "v".into(),
                subject: "p".into(),
                entity: "Pattern.Part".into(),
            },
        )]
    }
    #[test]
    fn unused_let_keeps_failed_and_pending_owned_call_conditions() {
        for pending in [false, true] {
            let map = fixture::MAP.replace(
                r#""field":"Pattern.Part.link","value":["v","p"]"#,
                r#""field":"Pattern.Part.link","value":["v","q"]"#,
            );
            let map = if pending {
                map.replace(r#"{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#, "")
            } else {
                map.replace(
                    r#""id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"]"#,
                    r#""id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","r2"]"#,
                )
            };
            assert_ne!(map, fixture::MAP);
            let inputs = fixture::with_body(
                &map,
                "view accept(r:Root,x:Part[r]):Bool=true;change bad(c:Part)=let ignored=accept(c.owner,c.link) in c with {flag=true};",
            );
            let environment = Environment::new(&inputs, &mut quiet()).unwrap();
            let update = evaluate(
                &environment,
                &inputs.law().declarations["Selected.bad"],
                &bindings(),
            )
            .unwrap();
            assert_eq!(
                update.state,
                if pending {
                    State::Undetermined
                } else {
                    State::ConditionFailed
                }
            );
            assert!(update.values.is_empty());
            if pending {
                assert!(
                    update
                        .missing
                        .iter()
                        .any(|f| f.subject == "q"
                            && f.field.as_deref() == Some("Pattern.Part.owner"))
                );
            }
        }
    }
    #[test]
    fn simultaneous_updates_read_the_same_original_state() {
        let inputs = fixture::with_body(
            fixture::MAP,
            "change swap(c:Part)=c with {quantity=c.other,other=c.quantity};",
        );
        let before = inputs.sources().clone();
        let environment = Environment::new(&inputs, &mut quiet()).unwrap();
        let update = evaluate(
            &environment,
            &inputs.law().declarations["Selected.swap"],
            &bindings(),
        )
        .unwrap();
        assert_eq!(update.state, State::Ready);
        assert_eq!(update.values.len(), 2);
        assert_eq!(
            update.values[0].0.field.as_deref(),
            Some("Pattern.Part.other")
        );
        assert_eq!(
            update.values[0].1,
            Scalar::Fp {
                modulus: "2".into(),
                value: 0.into()
            }
        );
        assert_eq!(
            update.values[1].1,
            Scalar::Fp {
                modulus: "2".into(),
                value: 1.into()
            }
        );
        assert_eq!(inputs.sources(), &before);
    }
    #[test]
    fn guarded_branch_and_let_use_the_parameter_without_updating_input() {
        let inputs = fixture::with_body(
            fixture::MAP,
            "change choose(c:Part,b:Bool) when b= c.flag = let n=c.other in if b then c with {quantity=n} else c with {quantity=c.quantity};",
        );
        let environment = Environment::new(&inputs, &mut quiet()).unwrap();
        for (b, state) in [(true, State::Ready), (false, State::Excluded)] {
            let mut bs = bindings();
            bs.push(("b".into(), Scalar::Bool(b)));
            let update = evaluate(
                &environment,
                &inputs.law().declarations["Selected.choose"],
                &bs,
            )
            .unwrap();
            assert_eq!(update.state, state);
            if b {
                assert_eq!(
                    update.values[0].1,
                    Scalar::Fp {
                        modulus: "2".into(),
                        value: 1.into()
                    }
                );
            } else {
                assert!(update.values.is_empty());
            }
        }
    }
    #[test]
    fn missing_update_value_is_not_an_empty_completed_update() {
        let inputs =
            fixture::with_body(fixture::MAP, "change keep(c:Part)=c with {third=c.third};");
        let environment = Environment::new(&inputs, &mut quiet()).unwrap();
        let update = evaluate(
            &environment,
            &inputs.law().declarations["Selected.keep"],
            &bindings(),
        )
        .unwrap();
        assert_eq!(update.state, State::Undetermined);
        assert!(update.values.is_empty());
        assert!(
            update
                .missing
                .iter()
                .any(|f| f.field.as_deref() == Some("Pattern.Part.third"))
        );
    }
    #[test]
    fn equal_update_states_keep_distinct_original_assignments_for_all_instances() {
        let inputs = fixture::with_body(
            fixture::MAP,
            "change zero(c:Part,b:Bool)=c with {quantity=0};",
        );
        let environment = Environment::new(&inputs, &mut quiet()).unwrap();
        let subjects = vec![
            bindings()[0].1.clone(),
            Scalar::Subject {
                snapshot: "v".into(),
                subject: "q".into(),
                entity: "Pattern.Part".into(),
            },
        ];
        let table = candidates(
            &environment,
            &inputs.law().declarations["Selected.zero"],
            &subjects,
        )
        .unwrap();
        assert!(table.complete);
        assert_eq!(table.rows.len(), 4);
        assert_eq!(table.parameter_types, vec![Type::Bool, Type::Bool]);
        assert_eq!(
            table
                .rows
                .iter()
                .map(|r| r.parameters.clone())
                .collect::<Vec<_>>(),
            vec![
                vec![Scalar::Bool(false), Scalar::Bool(false)],
                vec![Scalar::Bool(false), Scalar::Bool(true)],
                vec![Scalar::Bool(true), Scalar::Bool(false)],
                vec![Scalar::Bool(true), Scalar::Bool(true)],
            ]
        );
        for row in &table.rows {
            assert_eq!(row.update.state, State::Ready);
            assert_eq!(row.update.values, table.rows[0].update.values);
            assert_eq!(row.update.values.len(), 2);
        }
    }
    #[test]
    fn solutions_check_the_updated_state_and_keep_original_parameter_identity() {
        for (body, expected) in [
            (
                "change choose(c:Part,b:Bool)=c with {flag=b};law required valid(c:Part):c.flag;",
                vec![Some(false), Some(true)],
            ),
            (
                "change choose(c:Part,b:Bool)=c with {flag=true};law required valid(c:Part):c.flag;",
                vec![Some(true), Some(true)],
            ),
            (
                "change choose(c:Part,b:Bool)=c with {flag=false};law required valid(c:Part):c.flag;",
                vec![Some(false), Some(false)],
            ),
        ] {
            let inputs = fixture::with_body(fixture::MAP, body);
            let before = inputs.sources().clone();
            let environment = Environment::new(&inputs, &mut quiet()).unwrap();
            let table = candidates(
                &environment,
                &inputs.law().declarations["Selected.choose"],
                &[bindings()[0].1.clone()],
            )
            .unwrap();
            let requirements = vec![("Selected.valid".into(), bindings())];
            let rows = table
                .rows
                .iter()
                .enumerate()
                .map(|(point, candidate)| {
                    solution_row(&environment, candidate, point, &requirements).unwrap()
                })
                .collect::<Vec<_>>();
            assert_eq!(rows.iter().map(|r| r.member).collect::<Vec<_>>(), expected);
            assert_ne!(table.rows[0].parameters, table.rows[1].parameters);
            for row in rows {}
            assert_eq!(inputs.sources(), &before);
        }
    }
}
