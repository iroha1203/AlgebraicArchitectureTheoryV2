//! 共通修復問題を消費する問いの閉じた構文・型。
use super::*;
pub(super) fn is_custom(r: &Request) -> bool {
    matches!(
        r.kind,
        QuestionKind::Scopes
            | QuestionKind::Candidate
            | QuestionKind::Apply
            | QuestionKind::Observe
    ) || (r.kind == QuestionKind::Solve && matches!(r.head, Selector::Answer { .. }))
}
pub(super) fn resolve(
    raw: RawRequest,
    text: &str,
    kind: QuestionKind,
    c: &Control,
) -> Result<Request, ResolveFailure> {
    phase(c, Checkpoint::RequestBinding)?;
    let Selector::Answer { id, path } = &raw.head else {
        return Err(invalid(problem(
            RequestIssueCode::Type,
            &raw.id,
            "head",
            "specify a typed result Handle",
        )));
    };
    if path.is_empty() {
        return Err(invalid(problem(
            RequestIssueCode::Projection,
            &raw.id,
            "head",
            "specify an output field",
        )));
    }
    let mut dependencies = BTreeSet::from([id.clone()]);
    let mut arguments = BTreeMap::new();
    for (key, value) in raw.arguments {
        phase(c, Checkpoint::RequestBinding)?;
        let valid = match (kind, key.as_str(), &value) {
            (QuestionKind::Solve, "mode", Selector::Enum { value }) => {
                matches!(value.as_str(), "existence" | "solutions")
            }
            (QuestionKind::Candidate, "index", Selector::Ordinal { .. }) => true,
            (QuestionKind::Solve, "within", Selector::Answer { id, path })
            | (QuestionKind::Apply, "in", Selector::Answer { id, path })
                if !path.is_empty() =>
            {
                dependencies.insert(id.clone());
                true
            }
            _ => false,
        };
        if !valid {
            return Err(invalid(problem(
                RequestIssueCode::Type,
                &raw.id,
                &key,
                "unsupported argument or argument type for this repair operation",
            )));
        }
        arguments.insert(
            key.clone(),
            RequestArgument {
                name: key,
                value,
                origin: ArgumentOrigin::Explicit,
            },
        );
    }
    let required = match kind {
        QuestionKind::Solve => Some("within"),
        QuestionKind::Candidate => Some("index"),
        QuestionKind::Apply => Some("in"),
        _ => None,
    };
    if let Some(key) = required
        && !arguments.contains_key(key)
    {
        return Err(invalid(problem(
            RequestIssueCode::MissingBinding,
            &raw.id,
            key,
            "missing required repair argument",
        )));
    }
    if kind == QuestionKind::Solve && !arguments.contains_key("mode") {
        arguments.insert(
            "mode".into(),
            RequestArgument {
                name: "mode".into(),
                value: Selector::Enum {
                    value: "solutions".into(),
                },
                origin: ArgumentOrigin::Defaulted,
            },
        );
    }
    Ok(Request {
        id: raw.id,
        text: text.into(),
        kind,
        head: raw.head,
        arguments: arguments.into_values().collect(),
        dependencies: dependencies.into_iter().collect(),
        defaults: vec![],
        constraints: vec![],
    })
}
fn plan(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    s: &Selector,
    c: &Control,
) -> Result<ProjectionType, ResolveFailure> {
    selector_type(law, map, requests, names, s, c, (&r.id, "head")).map(|(p, _)| p.ty)
}
fn root(t: ProjectionType) -> Option<String> {
    match t {
        ProjectionType::RepairProblem(r)
        | ProjectionType::ChangeRange(r)
        | ProjectionType::RangeList(r)
        | ProjectionType::RepairObservation(r)
        | ProjectionType::Selection(r)
        | ProjectionType::SolutionSet(r)
        | ProjectionType::Assignment(r) => Some(r),
        _ => None,
    }
}
pub(super) fn output_type(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    field: &str,
    c: &Control,
) -> Result<ProjectionType, ResolveFailure> {
    let fail = || {
        invalid(problem(
            RequestIssueCode::Projection,
            &r.id,
            field,
            "output of this repair operation is not public",
        ))
    };
    if field == "proposition" {
        return Ok(ProjectionType::Proposition);
    }
    let owner = if r.kind == QuestionKind::Prepare {
        let mut b = r.clone();
        b.head = Selector::Declaration {
            name: law.declarations()[r.declaration().ok_or_else(fail)?]
                .reading
                .clone(),
        };
        let roots = build::root_types(law, map, requests, names, &b, c)?;
        roots.into_iter().next().ok_or_else(fail)?
    } else {
        let selector = if r.kind == QuestionKind::Observe {
            &r.arguments
                .iter()
                .find(|a| a.name == "on")
                .ok_or_else(fail)?
                .value
        } else {
            &r.head
        };
        root(plan(law, map, requests, names, r, selector, c)?).ok_or_else(fail)?
    };
    Ok(match (r.kind, field) {
        (QuestionKind::Observe, "plan") => ProjectionType::RepairObservation(owner),
        (QuestionKind::Observe, "solutions") => ProjectionType::SolutionSet(owner),
        (QuestionKind::Prepare, "problem") => ProjectionType::RepairProblem(owner),
        (QuestionKind::Solve, "solutions") => ProjectionType::SolutionSet(owner),
        (QuestionKind::Solve, "range") => ProjectionType::ChangeRange(owner),
        (QuestionKind::Scopes, "ranges") => ProjectionType::RangeList(owner),
        (QuestionKind::Candidate, "assignment") => ProjectionType::Assignment(owner),
        (QuestionKind::Apply, "selection") => ProjectionType::Selection(owner),
        (QuestionKind::Apply, "object") => ProjectionType::ArchitectureRoot(owner),
        _ => return Err(fail()),
    })
}
pub(super) fn origin<'a>(
    r: &'a Request,
    requests: &'a [Request],
    names: &BTreeMap<String, usize>,
) -> Option<&'a Request> {
    let mut current = r;
    for _ in 0..=requests.len() {
        if current.kind == QuestionKind::Prepare {
            return Some(current);
        }
        let head = if current.kind == QuestionKind::Observe {
            &current.arguments.iter().find(|a| a.name == "on")?.value
        } else {
            &current.head
        };
        let Selector::Answer { id, .. } = head else {
            return None;
        };
        current = &requests[*names.get(id)?];
    }
    None
}
pub(super) fn check_internal(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    c: &Control,
) -> Result<(), ResolveFailure> {
    if let Some(RequestArgument {
        value: Selector::Declaration { name },
        ..
    }) = r.arguments.iter().find(|a| a.name == "inputs")
    {
        let Signature::View { params, .. } = &law.declarations()[name].signature else {
            unreachable!()
        };
        let Signature::Law {
            params: original, ..
        } = &law.declarations()[r.declaration().expect("prepare Law")].signature
        else {
            unreachable!()
        };
        for parameter in params {
            if !original
                .iter()
                .any(|p| p.name == parameter.name && p.ty.erase() == parameter.ty.erase())
                || !r
                    .arguments
                    .iter()
                    .any(|a| a.name == format!("bind.{}", parameter.name))
            {
                return Err(invalid(problem(
                    RequestIssueCode::Type,
                    &r.id,
                    "inputs",
                    "input view parameters must be explicit Law bindings with the same names and types",
                )));
            }
        }
    }
    if let Some(a) = r.arguments.iter().find(|a| a.name == "internal") {
        let Some(Selector::Declaration { name }) = r
            .arguments
            .iter()
            .find(|a| a.name == "using")
            .map(|a| &a.value)
        else {
            return Err(invalid(problem(
                RequestIssueCode::Type,
                &r.id,
                "using",
                "missing change",
            )));
        };
        let Signature::Change { params, .. } = &law.declarations()[name].signature else {
            unreachable!()
        };
        let ty = plan(law, map, requests, names, r, &a.value, c)?;
        if !projection::can_bind_controlled(&ty, &Type::Set(Box::new(params[0].ty.erase())), c)
            .map_err(stopped)?
        {
            return Err(invalid(problem(
                RequestIssueCode::Type,
                &r.id,
                "internal",
                "internal must be a Set of the change entity type",
            )));
        }
    }
    Ok(())
}
pub(super) fn check(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    c: &Control,
) -> Result<(), ResolveFailure> {
    if r.kind == QuestionKind::Observe {
        return super::observation::check(law, map, requests, names, r, c);
    }
    let ty = plan(law, map, requests, names, r, &r.head, c)?;
    let valid = match r.kind {
        QuestionKind::Solve | QuestionKind::Scopes => {
            matches!(ty, ProjectionType::RepairProblem(_))
        }
        QuestionKind::Candidate => matches!(ty, ProjectionType::SolutionSet(_)),
        QuestionKind::Apply => matches!(ty, ProjectionType::Assignment(_)),
        _ => false,
    };
    if !valid {
        return Err(invalid(problem(
            RequestIssueCode::Type,
            &r.id,
            "head",
            "Handle has the wrong repair result type",
        )));
    }
    if let Some(a) = r.arguments.iter().find(|a| a.name == "within") {
        let within = plan(law, map, requests, names, r, &a.value, c)?;
        let valid = if matches!(within, ProjectionType::ChangeRange(_)) {
            true
        } else if let Some(p) = origin(r, requests, names) {
            let Some(Selector::Declaration { name }) = p
                .arguments
                .iter()
                .find(|a| a.name == "using")
                .map(|a| &a.value)
            else {
                unreachable!()
            };
            let Signature::Change { params, .. } = &law.declarations()[name].signature else {
                unreachable!()
            };
            projection::can_bind_controlled(&within, &Type::Set(Box::new(params[0].ty.erase())), c)
                .map_err(stopped)?
        } else {
            false
        };
        if !valid {
            return Err(invalid(problem(
                RequestIssueCode::Type,
                &r.id,
                "within",
                "within must be an entity Set or a ChangeRange",
            )));
        }
    }
    if let Some(a) = r.arguments.iter().find(|a| a.name == "in")
        && !matches!(
            plan(law, map, requests, names, r, &a.value, c)?,
            ProjectionType::SolutionSet(_)
        )
    {
        return Err(invalid(problem(
            RequestIssueCode::Type,
            &r.id,
            "in",
            "in must be a SolutionSet",
        )));
    }
    Ok(())
}
pub(super) fn projection(
    ty: &ProjectionType,
    path: &[ProjectionStep],
) -> Option<Result<(ProjectionPlan, usize), projection::ProjectionFailure>> {
    let owner = match ty {
        ProjectionType::RepairProblem(r)
        | ProjectionType::ChangeRange(r)
        | ProjectionType::RangeList(r)
        | ProjectionType::RepairObservation(r)
        | ProjectionType::Selection(r) => r,
        _ => return None,
    };
    let next = match (ty, path.first()) {
        (ProjectionType::RepairObservation(_), Some(ProjectionStep::Field(f))) => {
            match f.as_str() {
                "problem" => ProjectionType::RepairProblem(owner.clone()),
                "range" => ProjectionType::ChangeRange(owner.clone()),
                _ => return Some(Err("RepairObservation projection is not public".into())),
            }
        }
        (ProjectionType::RepairProblem(_), Some(ProjectionStep::Field(f))) => match f.as_str() {
            "domain" => ProjectionType::CandidateSpace(owner.clone()),
            "internal" | "units" => ProjectionType::Domain,
            _ => return Some(Err("RepairProblem projection is not public".into())),
        },
        (ProjectionType::ChangeRange(_), Some(ProjectionStep::Field(f))) => match f.as_str() {
            "problem" => ProjectionType::RepairProblem(owner.clone()),
            "enabled" => ProjectionType::Domain,
            _ => return Some(Err("ChangeRange projection is not public".into())),
        },
        (ProjectionType::RangeList(_), Some(ProjectionStep::Index(_))) => {
            ProjectionType::ChangeRange(owner.clone())
        }
        (ProjectionType::Selection(_), Some(ProjectionStep::Field(f))) => match f.as_str() {
            "domain" => ProjectionType::CandidateSpace(owner.clone()),
            "solutions" => ProjectionType::SolutionSet(owner.clone()),
            "parameters" => ProjectionType::Assignment(owner.clone()),
            "object" => ProjectionType::ArchitectureRoot(owner.clone()),
            _ => return Some(Err("Selection projection is not public".into())),
        },
        _ => return Some(Err("invalid repair projection".into())),
    };
    Some(Ok((
        ProjectionPlan {
            ty: next,
            conditional: matches!(ty, ProjectionType::RangeList(_)),
        },
        1,
    )))
}
