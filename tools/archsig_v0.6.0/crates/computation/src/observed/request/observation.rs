//! 有限修復の観測目的と許可読取りの閉じた入口。
use super::*;
pub(super) fn resolve(
    law: &CheckedLaw,
    raw: RawRequest,
    text: &str,
    c: &Control,
) -> Result<Request, ResolveFailure> {
    phase(c, Checkpoint::RequestBinding)?;
    let mut head = raw.head;
    let mut params = vec![];
    let mut dependencies = BTreeSet::new();
    match &head {
        Selector::Declaration { name } => {
            let name = declaration(law, name, c, &raw.id)?;
            let Signature::View {
                params: declared, ..
            } = &law.declarations()[&name].signature
            else {
                return Err(invalid(problem(
                    RequestIssueCode::Type,
                    &raw.id,
                    "head",
                    "observe requires a view or RepairObservation Handle",
                )));
            };
            params = declared.iter().map(|p| p.name.clone()).collect();
            head = Selector::Declaration { name };
        }
        Selector::Answer { id, path } if !path.is_empty() => {
            dependencies.insert(id.clone());
        }
        _ => {
            return Err(invalid(problem(
                RequestIssueCode::Type,
                &raw.id,
                "head",
                "observe requires a view or RepairObservation Handle",
            )));
        }
    }
    let mut arguments = BTreeMap::new();
    for (key, value) in raw.arguments {
        phase(c, Checkpoint::RequestBinding)?;
        let parameter = key.strip_prefix("bind.").unwrap_or(&key);
        let fixed = matches!(key.as_str(), "on" | "within" | "output");
        let valid = if key == "output" {
            matches!(&value,Selector::Enum{value} if matches!(value.as_str(),"decision"|"assignment"))
        } else if matches!(key.as_str(), "on" | "within") {
            matches!(&value,Selector::Answer{path,..} if !path.is_empty())
        } else {
            params.iter().any(|p| p == parameter)
                && (matches!(&value, Selector::Subject { .. })
                    || matches!(&value,Selector::Answer{path,..} if !path.is_empty()))
        };
        if !valid {
            return Err(invalid(problem(
                RequestIssueCode::Type,
                &raw.id,
                &key,
                "unsupported observation argument or argument type",
            )));
        }
        if let Selector::Answer { id, .. } = &value {
            dependencies.insert(id.clone());
        }
        let name = if fixed {
            key.clone()
        } else {
            format!("bind.{parameter}")
        };
        if arguments
            .insert(
                name.clone(),
                RequestArgument {
                    name,
                    value,
                    origin: ArgumentOrigin::Explicit,
                },
            )
            .is_some()
        {
            return Err(invalid(problem(
                RequestIssueCode::DuplicateArgument,
                &raw.id,
                &key,
                "duplicate binding for the same parameter",
            )));
        }
    }
    for key in ["on", "within", "output"]
        .into_iter()
        .map(str::to_owned)
        .chain(params.iter().map(|p| format!("bind.{p}")))
    {
        if !arguments.contains_key(&key) {
            return Err(invalid(problem(
                RequestIssueCode::MissingBinding,
                &raw.id,
                &key,
                "missing observation argument or view binding",
            )));
        }
    }
    Ok(Request {
        id: raw.id,
        text: text.into(),
        kind: QuestionKind::Observe,
        head,
        arguments: arguments.into_values().collect(),
        dependencies: dependencies.into_iter().collect(),
        defaults: vec![],
        constraints: vec![],
    })
}
pub(super) fn check(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    c: &Control,
) -> Result<(), ResolveFailure> {
    let on = r.arguments.iter().find(|a| a.name == "on").ok_or_else(|| {
        invalid(problem(
            RequestIssueCode::MissingBinding,
            &r.id,
            "on",
            "missing observation problem",
        ))
    })?;
    let ty = selector_type(law, map, requests, names, &on.value, c, (&r.id, "on"))?
        .0
        .ty;
    if !matches!(ty, ProjectionType::RepairProblem(_)) {
        return Err(invalid(problem(
            RequestIssueCode::Type,
            &r.id,
            "on",
            "observe requires a RepairProblem",
        )));
    }
    if let Selector::Declaration { name } = &r.head {
        let Signature::View { params, .. } = &law.declarations()[name].signature else {
            unreachable!()
        };
        for parameter in params {
            phase(c, Checkpoint::RequestBinding)?;
            let value = &r
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", parameter.name))
                .expect("全束縛を検査済み")
                .value;
            let ty = selector_type(
                law,
                map,
                requests,
                names,
                value,
                c,
                (&r.id, &parameter.name),
            )?
            .0
            .ty;
            if !projection::can_bind_controlled(&ty, &parameter.ty.erase(), c).map_err(stopped)? {
                return Err(invalid(problem(
                    RequestIssueCode::Type,
                    &r.id,
                    &parameter.name,
                    "observation binding has the wrong type",
                )));
            }
        }
    } else {
        let ty = selector_type(law, map, requests, names, &r.head, c, (&r.id, "head"))?
            .0
            .ty;
        if !matches!(ty, ProjectionType::RepairObservation(_)) {
            return Err(invalid(problem(
                RequestIssueCode::Type,
                &r.id,
                "head",
                "observe requires a RepairObservation Handle",
            )));
        }
    }
    let mut solve = r.clone();
    solve.kind = QuestionKind::Solve;
    solve.head = on.value.clone();
    repair_problem::check(law, map, requests, names, &solve, c)?;
    let origin = repair_problem::origin(&solve, requests, names).ok_or_else(|| {
        invalid(problem(
            RequestIssueCode::Type,
            &r.id,
            "on",
            "observation problem has no prepare origin",
        ))
    })?;
    if !origin.arguments.iter().any(|a| a.name == "inputs") {
        return Err(invalid(problem(
            RequestIssueCode::Type,
            &r.id,
            "on",
            "prepare inputs=View before asking for observation sufficiency",
        )));
    }
    Ok(())
}
