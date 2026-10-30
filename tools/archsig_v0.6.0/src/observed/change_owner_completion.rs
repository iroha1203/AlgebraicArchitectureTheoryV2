//! 有限補完の各候補族を再生成し、具体構成と別に存在・一意性を検査する。
use super::*;
use crate::observed::{data, environment::change_evaluation};
use std::collections::BTreeSet;

type Computed = (Vec<Part>, Answer, Option<change_search::Search>);

fn decision(counts: &[usize], unique: bool) -> Decision {
    let test = |count: &usize| if unique { *count == 1 } else { *count > 0 };
    if counts.iter().all(test) {
        Decision::Established
    } else if counts.iter().all(|count| !test(count)) {
        Decision::Refuted
    } else {
        Decision::Undetermined
    }
}

pub(super) fn compute(
    env: &Environment<'_>,
    g: &Graph,
    architecture: &Architecture,
    base: usize,
    request: &Request,
    c: &mut Control,
    value_fields: &[Fact],
) -> Result<Option<Computed>, ValidationFailure> {
    let fields = if value_fields.is_empty() {
        architecture
            .witness
            .construction()
            .local_domain()
            .conditional()
            .iter()
            .map(|member| member.owner_slot().clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
    } else {
        value_fields.to_vec()
    };
    if fields.is_empty()
        || architecture.reasons.iter().any(|reason| {
            !matches!(reason.kind, ReasonKind::Missing)
                || reason.missing.iter().any(|fact| !fields.contains(fact))
        })
    {
        return Ok(None);
    }
    let name = request.declaration().ok_or("補完solveのLawがない")?;
    let declaration = &env.inputs.law().declarations[name];
    let Signature::Law { body, params, .. } = &declaration.signature else {
        return Err("補完solveがLawでない".into());
    };
    let enumeration = match env.completion_assignments(&fields, &mut |_, _| {}) {
        Ok(enumeration) => enumeration,
        Err(ValidationFailure::UnsupportedExpression { .. }) if !value_fields.is_empty() => {
            return Ok(None);
        }
        Err(failure) => return Err(failure),
    };
    if enumeration.values.is_empty() {
        return Err("検査済み入力のowner補完が空".into());
    }
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let expression = source_expression(
        &mut b,
        env,
        *body,
        &[],
        &params
            .iter()
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect::<Vec<_>>(),
    )?;
    let reason = Reason {
        kind: ReasonKind::Missing,
        request: request.id.clone(),
        dependencies: vec![expression],
        missing: fields.clone(),
        location: Some(Location::Law {
            span: declaration.span,
        }),
    };
    let solutions = b.push(
        NodeType::Construction(T::SolutionSet),
        "solution_set",
        Json::obj([]),
        vec![expression, architecture.root],
        None,
        None,
    )?;
    b.parts[solutions.0 - base].reasons = vec![reason.clone()];
    b.parts[solutions.0 - base].scope.merge(&enumeration.scope);
    b.parts[solutions.0 - base]
        .support
        .extend(enumeration.support.iter().cloned());
    b.parts[solutions.0 - base].support.sort();
    b.parts[solutions.0 - base].support.dedup();
    let mut cases = vec![];
    let mut counts = vec![];
    let mut arguments = vec![expression, solutions];
    for value_ in enumeration.values {
        c.checkpoint(Checkpoint::Completion)?;
        let values = if fields.len() == 1 {
            vec![value_]
        } else {
            let Scalar::Tuple(ref values) = value_ else {
                return Err("owner補完のslot積が違う".into());
            };
            values.clone()
        };
        if values.len() != fields.len() {
            return Err("owner補完の位置数が違う".into());
        }
        let completions = fields
            .iter()
            .cloned()
            .zip(values.iter().cloned())
            .collect::<Vec<_>>();
        let search = change_search::search_with_completions(
            env,
            g,
            &architecture.witness,
            request,
            &completions,
            c,
        )
        .map_err(|failure| failure.cause)?;
        let candidates = search
            .candidates
            .as_ref()
            .ok_or("owner補完に有限候補表がない")?;
        if !value_fields.is_empty() {
            let additional = search
                .missing
                .iter()
                .cloned()
                .chain(
                    candidates
                        .rows
                        .iter()
                        .flat_map(|row| row.update.missing.iter().cloned()),
                )
                .filter(|fact| !fields.contains(fact))
                .collect::<BTreeSet<_>>();
            if !additional.is_empty() {
                let expanded = fields
                    .iter()
                    .cloned()
                    .chain(additional)
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>();
                return stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
                    compute(env, g, architecture, base, request, c, &expanded)
                });
            }
        }
        if !search.complete
            || !candidates.complete
            || search.linear.is_some()
            || search.rational.is_some()
            || !search.missing.is_empty()
            || search.solutions.iter().any(|row| row.member.is_none())
            || candidates.rows.iter().any(|row| {
                row.update.state == change_evaluation::State::Undetermined
                    || !row.update.missing.is_empty()
            })
        {
            return Err(ValidationFailure::UnsupportedExpression {
                location: Location::Law {
                    span: declaration.span,
                },
                feature: "owner以外の欠測・非有限候補の補完配送は未実装".into(),
            });
        }
        let width = candidates.parameter_types.len() / candidates.subjects.len().max(1);
        let values = values
            .iter()
            .map(|scalar| value(&mut b, scalar))
            .collect::<Result<Vec<_>, _>>()?;
        arguments.extend(&values);
        let mut assignments = vec![];
        let mut original_points: Vec<Vec<Scalar>> = vec![];
        for row in &search.solutions {
            c.checkpoint(Checkpoint::Completion)?;
            if row.member != Some(true) {
                continue;
            }
            change_search::verify_point(env, &architecture.witness, &search, row.candidate, c)?;
            let point = candidates
                .rows
                .get(row.candidate)
                .ok_or("補完解の元候補がない")?;
            let mut duplicate = false;
            for previous in &original_points {
                let mut equal = previous.len() == point.parameters.len();
                for (left, right) in previous.iter().zip(&point.parameters) {
                    equal &= data::equal(left, right, c)?;
                }
                if equal {
                    duplicate = true;
                    break;
                }
            }
            if duplicate {
                continue;
            }
            original_points.push(point.parameters.clone());
            let mut entries = vec![];
            for (index, subject) in candidates.subjects.iter().enumerate() {
                let subject = value(&mut b, subject)?;
                let parameters = point.parameters[index * width..(index + 1) * width]
                    .iter()
                    .map(|scalar| value(&mut b, scalar))
                    .collect::<Result<Vec<_>, _>>()?;
                arguments.push(subject);
                arguments.extend(&parameters);
                entries.push(Json::obj([
                    ("subject", subject.wire()),
                    ("parameters", refs(&parameters)),
                ]));
            }
            // 重複した表示を解の数にしない。比較対象は元subjectと元parameter値。
            assignments.push(Json::Arr(entries));
        }
        counts.push(assignments.len());
        cases.push(Json::obj([
            ("values", refs(&values)),
            ("assignments", Json::Arr(assignments)),
        ]));
    }
    let certificate = b.push(
        NodeType::Evidence,
        "evidence",
        Json::obj([
            ("kind", Json::str("completion_fibers")),
            (
                "data",
                Json::obj([
                    ("request", Json::str(&request.id)),
                    ("solutions", solutions.wire()),
                    ("fields", Json::Arr(fields.iter().map(Fact::wire).collect())),
                    ("cases", Json::Arr(cases)),
                ]),
            ),
        ]),
        arguments,
        None,
        None,
    )?;
    b.parts[certificate.0 - base].reasons.clear();
    b.parts[certificate.0 - base].scope.completions = true;
    let existence_status = decision(&counts, false);
    let unique_status = decision(&counts, true);
    let existence = proof(
        &mut b,
        "inhabited",
        solutions,
        certificate,
        existence_status,
        &reason,
    )?;
    let unique = proof(
        &mut b,
        "unique_solution",
        solutions,
        certificate,
        unique_status,
        &reason,
    )?;
    let mut outputs = BTreeMap::from([("proposition".into(), existence)]);
    let (claim, status, reasons) = if request.kind == QuestionKind::Repair {
        outputs.insert("existence".into(), existence);
        let label = value(&mut b, &Scalar::Text("repair".into()))?;
        let status = if unique_status == Decision::Refuted {
            Decision::Refuted
        } else {
            Decision::Undetermined
        };
        let claim = b.proposition(
            "constructible",
            vec![label],
            vec![unique, existence],
            status,
        )?;
        b.parts[claim.0 - base].reasons.clear();
        b.parts[claim.0 - base]
            .judgment
            .as_mut()
            .ok_or("補完修復判断がない")?
            .reasons
            .clear();
        let reasons = if status == Decision::Refuted {
            vec![Reason {
                kind: ReasonKind::ConditionFailed {
                    condition: unique,
                    construction: "repair",
                },
                request: request.id.clone(),
                dependencies: vec![unique],
                missing: vec![],
                location: Some(Location::Law {
                    span: declaration.span,
                }),
            }]
        } else if !value_fields.is_empty() {
            vec![reason.clone()]
        } else {
            let mut reasons = vec![Reason {
                kind: ReasonKind::Internal("repair concrete construction (not implemented)".into()),
                request: request.id.clone(),
                dependencies: vec![certificate],
                missing: vec![],
                location: Some(Location::Law {
                    span: declaration.span,
                }),
            }];
            if unique_status == Decision::Undetermined {
                reasons.push(reason.clone());
            }
            reasons
        };
        b.parts[claim.0 - base].reasons = reasons.clone();
        b.parts[claim.0 - base]
            .judgment
            .as_mut()
            .ok_or("補完修復判断がない")?
            .reasons = reasons.clone();
        outputs.insert("proposition".into(), claim);
        (claim, status, reasons)
    } else if !value_fields.is_empty() && existence_status != Decision::Refuted {
        // The existence judgment is complete; concrete state values still depend on missing input.
        let label = value(&mut b, &Scalar::Text("solution_set".into()))?;
        let claim = b.proposition(
            "constructible",
            vec![label],
            vec![existence, certificate],
            Decision::Undetermined,
        )?;
        let part = &mut b.parts[claim.0 - base];
        part.reasons = vec![reason.clone()];
        part.judgment
            .as_mut()
            .ok_or("有限補完の構成判断がない")?
            .reasons = vec![reason.clone()];
        (claim, Decision::Undetermined, vec![reason])
    } else {
        (
            existence,
            existence_status,
            if existence_status == Decision::Undetermined {
                vec![reason]
            } else {
                vec![]
            },
        )
    };
    let scope = b.parts[claim.0 - base].scope.clone();
    Ok(Some((
        b.parts,
        Answer {
            id: request.id.clone(),
            status,
            outputs,
            claim: Some(claim),
            evidence: vec![certificate],
            reasons,
            scope,
        },
        None,
    )))
}

fn proof(
    b: &mut Builder<'_>,
    predicate: &str,
    solutions: NodeRef,
    evidence: NodeRef,
    status: Decision,
    reason: &Reason,
) -> Result<NodeRef, ValidationFailure> {
    let r = b.proposition(predicate, vec![solutions], vec![evidence], status)?;
    let part = &mut b.parts[r.0 - b.base];
    let reasons = if status == Decision::Undetermined {
        vec![reason.clone()]
    } else {
        vec![]
    };
    part.reasons = reasons.clone();
    part.evidence = vec![evidence];
    let judgment = part.judgment.as_mut().ok_or("補完判断がない")?;
    judgment.reasons = reasons;
    judgment.evidence = vec![evidence];
    Ok(r)
}

#[cfg(test)]
#[path = "change_owner_completion_tests.rs"]
mod tests;
