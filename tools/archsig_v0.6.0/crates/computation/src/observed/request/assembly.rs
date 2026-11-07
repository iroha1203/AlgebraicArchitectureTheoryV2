//! 局所モデル組立ての、View・明示束縛・原始rootに閉じた構文と型。
use super::*;
fn error(id: &str, arg: &str, message: &str) -> ResolveFailure {
    invalid(problem(RequestIssueCode::Type, id, arg, message))
}
pub(super) fn root_type<'a>(law: &'a CheckedLaw, r: &Request) -> Result<&'a str, ResolveFailure> {
    let Some(name) = r.declaration() else {
        return Err(error(&r.id, "head", "assemble requires a view"));
    };
    let Signature::View {
        returns: Type::Set(t),
        ..
    } = &law.declarations()[name].signature
    else {
        return Err(error(&r.id, "head", "fragment view must return Set<Root>"));
    };
    let Type::Ref(root) = t.as_ref() else {
        return Err(error(
            &r.id,
            "head",
            "fragment view must return root references",
        ));
    };
    if !matches!(
        law.definitions()
            .declarations()
            .get(root)
            .map(|d| &d.signature),
        Some(archsig_input::definition::PrimitiveSignature::Entity { owner: None, .. })
    ) {
        return Err(error(
            &r.id,
            "head",
            "fragment type must be an ownerless entity",
        ));
    }
    Ok(root)
}
pub(super) fn resolve(
    law: &CheckedLaw,
    raw: RawRequest,
    text: &str,
    c: &Control,
) -> Result<Request, ResolveFailure> {
    phase(c, Checkpoint::RequestBinding)?;
    let Selector::Declaration { name } = &raw.head else {
        return Err(error(&raw.id, "head", "assemble requires a view"));
    };
    let name = declaration(law, name, c, &raw.id)?;
    let Signature::View { params, .. } = &law.declarations()[&name].signature else {
        return Err(error(&raw.id, "head", "assemble requires a view"));
    };
    let mut arguments = BTreeMap::new();
    let mut dependencies = BTreeSet::new();
    for (key, value) in raw.arguments {
        phase(c, Checkpoint::RequestBinding)?;
        let (name, value) = if key == "along" {
            let Selector::Declaration { name } = &value else {
                return Err(error(&raw.id, &key, "along must name a view"));
            };
            let name = declaration(law, name, c, &raw.id)?;
            (key.clone(), Selector::Declaration { name })
        } else {
            let parameter = key.strip_prefix("bind.").unwrap_or(&key);
            if key != "on" && !params.iter().any(|p| p.name == parameter) {
                return Err(error(&raw.id, &key, "unknown assembly argument"));
            }
            if !matches!(&value, Selector::Subject { .. })
                && !matches!(&value,Selector::Answer{path,..} if !path.is_empty())
            {
                return Err(error(&raw.id, &key, "specify a typed root or value Handle"));
            }
            if let Selector::Answer { id, .. } = &value {
                dependencies.insert(id.clone());
            }
            (
                if key == "on" {
                    key.clone()
                } else {
                    format!("bind.{parameter}")
                },
                value,
            )
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
                "duplicate assembly argument",
            )));
        }
    }
    for key in ["on".to_owned(), "along".to_owned()]
        .into_iter()
        .chain(params.iter().map(|p| format!("bind.{}", p.name)))
    {
        if !arguments.contains_key(&key) {
            return Err(invalid(problem(
                RequestIssueCode::MissingBinding,
                &raw.id,
                &key,
                "missing assembly argument or view binding",
            )));
        }
    }
    let r = Request {
        id: raw.id,
        text: text.into(),
        kind: QuestionKind::Assemble,
        head: Selector::Declaration { name },
        arguments: arguments.into_values().collect(),
        defaults: vec![],
        dependencies: dependencies.into_iter().collect(),
        constraints: vec![],
    };
    root_type(law, &r)?;
    Ok(r)
}
pub(super) fn check(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    c: &Control,
) -> Result<Vec<BindingConstraint>, ResolveFailure> {
    let root = root_type(law, r)?;
    let head = &law.declarations()[r.declaration().unwrap()];
    let Signature::View { params, .. } = &head.signature else {
        unreachable!()
    };
    let Some(RequestArgument {
        value: Selector::Declaration { name },
        ..
    }) = r.arguments.iter().find(|a| a.name == "along")
    else {
        return Err(error(&r.id, "along", "missing interface view"));
    };
    let along = &law.declarations()[name];
    let Signature::View {
        params: other,
        returns,
        ..
    } = &along.signature
    else {
        return Err(error(&r.id, "along", "along must be a view"));
    };
    if head.reading != along.reading
        || params.len() != other.len()
        || params
            .iter()
            .zip(other)
            .any(|(a, b)| a.name != b.name || a.ty != b.ty)
    {
        return Err(error(
            &r.id,
            "along",
            "interface view must share the reading and named parameter types",
        ));
    }
    let mut pending = vec![returns];
    while let Some(ty) = pending.pop() {
        phase(c, Checkpoint::RequestBinding)?;
        if matches!(ty, Type::Unit) {
            continue;
        }
        if let Type::Tuple(types) = ty {
            pending.extend(types);
            continue;
        }
        let Type::List(pair) = ty else {
            return Err(error(
                &r.id,
                "along",
                "interfaces must be lists of typed reference pairs",
            ));
        };
        let Type::Tuple(pair) = pair.as_ref() else {
            return Err(error(&r.id, "along", "interface entry must be a pair"));
        };
        if pair.len() != 2 || pair[0] != pair[1] {
            return Err(error(
                &r.id,
                "along",
                "interface pair must have the same reference type",
            ));
        }
        let (Type::Ref(name) | Type::Owned(name, _)) = &pair[0] else {
            return Err(error(
                &r.id,
                "along",
                "interface pair must contain owned individuals",
            ));
        };
        if !matches!(law.definitions().declarations().get(name).map(|d|&d.signature),Some(archsig_input::definition::PrimitiveSignature::Entity{owner:Some(owner),..}|archsig_input::definition::PrimitiveSignature::Arrow{owner,..}) if owner==root)
        {
            return Err(error(
                &r.id,
                "along",
                "interface individual must belong to the fragment root type",
            ));
        }
    }
    let on = r.arguments.iter().find(|a| a.name == "on").unwrap();
    let (on, _) = selector_type(law, map, requests, names, &on.value, c, (&r.id, "on"))?;
    if on.ty != ProjectionType::Law(Type::Ref(root.into())) {
        return Err(error(
            &r.id,
            "on",
            "assembly root marker has a different type",
        ));
    }
    binding_constraints(law, map, requests, names, r, params, c)
}
pub(super) fn output_type(
    law: &CheckedLaw,
    r: &Request,
    field: &str,
) -> Result<ProjectionType, ResolveFailure> {
    let root = root_type(law, r)?.to_owned();
    Ok(match field {
        "proposition" => ProjectionType::Proposition,
        "object" => ProjectionType::ArchitectureRoot(root),
        "algebra" => ProjectionType::ObjectAlgebraRoot(root),
        "assembly" => ProjectionType::ModelAssembly(shape(law, r)?),
        _ => return Err(error(&r.id, field, "assembly output is not public")),
    })
}

pub(super) fn shape(
    law: &CheckedLaw,
    r: &Request,
) -> Result<super::super::projection::AssemblyProjection, ResolveFailure> {
    let Some(RequestArgument {
        value: Selector::Declaration { name },
        ..
    }) = r.arguments.iter().find(|a| a.name == "along")
    else {
        return Err(error(&r.id, "along", "missing shared view"));
    };
    let Signature::View { returns, .. } = &law.declarations()[name].signature else {
        return Err(error(&r.id, "along", "shared declaration must be a view"));
    };
    Ok(super::super::projection::AssemblyProjection {
        root: root_type(law, r)?.into(),
        reading: law.declarations()[r.declaration().unwrap()].reading.clone(),
        interfaces: returns.clone(),
    })
}
pub(super) fn project(
    law: &CheckedLaw,
    ty: &ProjectionType,
    path: &[ProjectionStep],
    c: &Control,
) -> Option<Result<(ProjectionPlan, usize), super::super::projection::ProjectionFailure>> {
    use super::super::projection::{MapProjection, OperationProjection, ProjectionFailure as F};
    let ProjectionType::ModelAssembly(shape) = ty else {
        return None;
    };
    let result = (|| {
        phase(c, Checkpoint::Projection).map_err(|e| match e {
            ResolveFailure::Interrupted { reason } => F::Interrupted(reason),
            _ => F::Invalid("assembly projection interrupted".into()),
        })?;
        let (result, used, conditional) = match path {
            [ProjectionStep::Field(f), ..] if f == "object" => (
                ProjectionType::ArchitectureRoot(shape.root.clone()),
                1,
                false,
            ),
            [ProjectionStep::Field(f), ..] if f == "algebra" => (
                ProjectionType::ObjectAlgebraRoot(shape.root.clone()),
                1,
                false,
            ),
            [ProjectionStep::Field(f), ..] if f == "fragments" => (
                ProjectionType::Law(Type::Set(Box::new(Type::Ref(shape.root.clone())))),
                1,
                false,
            ),
            [ProjectionStep::Field(f), ..] if f == "interfaces" => {
                (ProjectionType::Law(shape.interfaces.clone()), 1, false)
            }
            [
                ProjectionStep::Field(f),
                ProjectionStep::Index(_),
                ProjectionStep::Field(field),
                rest @ ..,
            ] if f == "inclusions" => {
                if field == "fragment" {
                    (
                        ProjectionType::ArchitectureRoot(shape.root.clone()),
                        3,
                        true,
                    )
                } else if field == "map" || field == "restriction" {
                    (
                        ProjectionType::ConfigurationMap(MapProjection {
                            declaration: String::new(),
                            source: shape.root.clone(),
                            target: shape.root.clone(),
                        }),
                        3,
                        true,
                    )
                } else if field == "generators" {
                    let [ProjectionStep::Index(_), ProjectionStep::Field(field), ..] = rest else {
                        return Err(F::Invalid("select a generator field".into()));
                    };
                    if field == "proposition" {
                        (ProjectionType::Proposition, 5, true)
                    } else if field == "source" || field == "target" {
                        let namespaces =
                            crate::construction::reading_namespaces(law, &shape.reading, c)
                                .map_err(|e| match e {
                                    crate::construction::ConstructionFailure::Stopped(s) => {
                                        F::Interrupted(s)
                                    }
                                    _ => F::Invalid("assembly reading is unavailable".into()),
                                })?;
                        let mut options = Vec::new();
                        for d in law.definitions().declarations().values() {
                            c.checkpoint(Checkpoint::Projection)?;
                            if let archsig_input::definition::PrimitiveSignature::Arrow {
                                owner,
                                endpoint,
                                ..
                            } = &d.signature
                                && owner == &shape.root
                                && namespaces.contains(&d.namespace)
                            {
                                options.push(ProjectionType::ComposedOperation(
                                    OperationProjection {
                                        source: endpoint.clone(),
                                        target: endpoint.clone(),
                                        reading: shape.reading.clone(),
                                        to_reading: shape.reading.clone(),
                                        word: vec![d.name.to_string()],
                                    },
                                ));
                            }
                        }
                        if options.len() == 1 {
                            (options.pop().unwrap(), 5, true)
                        } else {
                            (ProjectionType::Dynamic(options), 5, true)
                        }
                    } else {
                        return Err(F::Invalid("generator field is not public".into()));
                    }
                } else {
                    return Err(F::Invalid("inclusion field is not public".into()));
                }
            }
            _ => return Err(F::Invalid("ModelAssembly projection is not public".into())),
        };
        Ok((
            ProjectionPlan {
                ty: result,
                conditional,
            },
            used,
        ))
    })();
    Some(result)
}
