//! 局所化と診断の固定署名。既存のArchitecture/LocalSystemだけを対象にする。
use super::*;
fn err(r: &str, key: &str, message: &str) -> ResolveFailure {
    invalid(problem(RequestIssueCode::Type, r, key, message))
}
pub(super) fn resolve(
    law: &CheckedLaw,
    raw: RawRequest,
    text: &str,
    c: &mut Control,
) -> Result<Request, ResolveFailure> {
    let kind = if raw.kind == "localize" {
        QuestionKind::Localize
    } else {
        QuestionKind::Diagnose
    };
    let Selector::Answer { id, path } = &raw.head else {
        return Err(err(&raw.id, "head", "target must be a public result Handle"));
    };
    if path.is_empty() {
        return Err(err(&raw.id, "head", "specify an output field"));
    }
    let mut dependencies = BTreeSet::from([id.clone()]);
    let mut arguments = BTreeMap::new();
    let mut defaults = vec![];
    let mut selected = None;
    if kind == QuestionKind::Localize {
        for (key, value) in &raw.arguments {
            if matches!(key.as_str(), "law" | "using") {
                let Selector::Declaration { name } = value else {
                    return Err(err(&raw.id, key, "specify a declaration name"));
                };
                let full = declaration(law, name, c, &raw.id)?;
                if !matches!(
                    (&law.declarations[&full].signature, key.as_str()),
                    (Signature::Law { .. }, "law") | (Signature::Change { .. }, "using")
                ) {
                    return Err(err(&raw.id, key, "declaration kind does not match"));
                }
                if key == "law" {
                    selected = Some(full.clone());
                }
                arguments.insert(
                    key.clone(),
                    RequestArgument {
                        name: key.clone(),
                        value: Selector::Declaration { name: full },
                        origin: ArgumentOrigin::Explicit,
                    },
                );
            }
        }
        if !arguments.contains_key("using") {
            defaults.push(RequestDefault::IdentityChange);
        }
        if selected.is_none() {
            defaults.push(RequestDefault::RequiredLaws);
        }
    }
    for (key, value) in raw.arguments {
        phase(c, Checkpoint::RequestBinding)?;
        if matches!(key.as_str(), "law" | "using") && kind == QuestionKind::Localize {
            continue;
        }
        let canonical = if kind == QuestionKind::Diagnose {
            match (key.as_str(), &value) {
                ("degree", Selector::Degree { .. }) => {}
                ("side", Selector::Enum { value })
                    if matches!(value.as_str(), "equation" | "semantic") => {}
                _ => return Err(err(&raw.id, &key, "diagnose arguments must be degree and side")),
            }
            key.clone()
        } else {
            let Some(name) = &selected else {
                return Err(err(&raw.id, &key, "bindings cannot be specified when law is omitted"));
            };
            let Signature::Law { params, .. } = &law.declarations[name].signature else {
                unreachable!()
            };
            let short = key.strip_prefix("bind.").unwrap_or(&key);
            if !params.iter().any(|p| p.name == short) {
                return Err(err(&raw.id, &key, "parameter is not declared in Law"));
            }
            if !matches!(value, Selector::Subject { .. } | Selector::Answer { .. }) {
                return Err(err(&raw.id, &key, "binding must be a Handle"));
            }
            format!("bind.{short}")
        };
        if let Selector::Answer { id, .. } = &value {
            dependencies.insert(id.clone());
        }
        let a = RequestArgument {
            name: canonical.clone(),
            value,
            origin: ArgumentOrigin::Explicit,
        };
        if arguments.insert(canonical, a).is_some() {
            return Err(err(&raw.id, &key, "duplicate argument"));
        }
    }
    if kind == QuestionKind::Diagnose {
        for (name, value) in [
            ("degree", Selector::Degree { value: 1 }),
            (
                "side",
                Selector::Enum {
                    value: "equation".into(),
                },
            ),
        ] {
            arguments
                .entry(name.into())
                .or_insert_with(|| RequestArgument {
                    name: name.into(),
                    value,
                    origin: ArgumentOrigin::Defaulted,
                });
        }
    } else if let Some(name) = selected {
        let Signature::Law { params, .. } = &law.declarations[&name].signature else {
            unreachable!()
        };
        let parameters = params
            .iter()
            .filter(|p| !arguments.contains_key(&format!("bind.{}", p.name)))
            .map(|p| p.name.clone())
            .collect::<Vec<_>>();
        if !parameters.is_empty() {
            defaults.push(RequestDefault::UniversalParameters {
                declaration: name,
                parameters,
            });
        }
    }
    Ok(Request {
        id: raw.id,
        text: text.into(),
        kind,
        head: raw.head,
        arguments: arguments.into_values().collect(),
        defaults,
        dependencies: dependencies.into_iter().collect(),
        constraints: vec![],
    })
}
pub(super) fn check(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    c: &mut Control,
) -> Result<Vec<BindingConstraint>, ResolveFailure> {
    let (head, _) = selector_type(law, map, requests, names, &r.head, c, (&r.id, "head"))?;
    if !matches!(
        (r.kind, &head.ty),
        (
            QuestionKind::Localize,
            ProjectionType::Architecture | ProjectionType::ArchitectureRoot(_)
        ) | (QuestionKind::Diagnose, ProjectionType::LocalSystem)
    ) {
        return Err(err(&r.id, "head", "target result type does not match"));
    }
    if let Some(RequestArgument {
        value: Selector::Declaration { name },
        ..
    }) = r.arguments.iter().find(|a| a.name == "law")
    {
        let Signature::Law { params, .. } = &law.declarations[name].signature else {
            unreachable!()
        };
        return binding_constraints(law, map, requests, names, r, params, c);
    }
    Ok(vec![])
}
pub(super) fn output_type(r: &Request, field: &str) -> Result<ProjectionType, ResolveFailure> {
    match (r.kind, field) {
        (QuestionKind::Localize, "system") => Ok(ProjectionType::LocalSystem),
        (QuestionKind::Diagnose, "diagnostic") => Ok(ProjectionType::Diagnostic),
        (QuestionKind::Diagnose, "space") => Ok(ProjectionType::Cohomology),
        (QuestionKind::Diagnose, "class") if r.arguments.iter().any(|a| a.name == "degree" && a.value == Selector::Degree { value: 1 }) => Ok(ProjectionType::Class),
        (QuestionKind::Localize, "proposition") => Ok(ProjectionType::Proposition),
        (QuestionKind::Diagnose, "proposition")
            if r.arguments
                .iter()
                .any(|a| a.name == "degree" && a.value == Selector::Degree { value: 1 }) =>
        {
            Ok(ProjectionType::Proposition)
        }
        _ => Err(err(&r.id, field, "localization or diagnostic output is not public")),
    }
}
