//! 担当別correspondenceの明示束縛と、二つのnative ModelAssemblyの型。
use super::*;
use crate::observed::projection::{MapAssemblyProjection, MapProjection, ProjectionFailure};
fn error(id: &str, key: &str, message: &str) -> ResolveFailure {
    invalid(problem(RequestIssueCode::Type, id, key, message))
}
fn correspondence<'a>(
    law: &'a CheckedLaw,
    r: &Request,
) -> Result<(&'a str, &'a str), ResolveFailure> {
    let Some(name) = r.declaration() else {
        return Err(error(&r.id, "head", "assemble_map requires a view"));
    };
    let Signature::View {
        returns: Type::Set(t),
        ..
    } = &law.declarations()[name].signature
    else {
        return Err(error(
            &r.id,
            "head",
            "correspondence view must return Set<C>",
        ));
    };
    let Type::Ref(ty) = t.as_ref() else {
        return Err(error(
            &r.id,
            "head",
            "correspondence view must return references",
        ));
    };
    let Some(d) = law.definitions().declarations().get(ty) else {
        return Err(error(&r.id, "head", "correspondence type is absent"));
    };
    let archsig_input::definition::PrimitiveSignature::Correspondence { from, to, .. } =
        &d.signature
    else {
        return Err(error(
            &r.id,
            "head",
            "view element must be a primitive correspondence",
        ));
    };
    if from != to {
        return Err(error(
            &r.id,
            "head",
            "assembly correspondence must have one root type",
        ));
    }
    Ok((ty, from))
}
pub(super) fn resolve(
    law: &CheckedLaw,
    raw: RawRequest,
    text: &str,
    c: &Control,
) -> Result<Request, ResolveFailure> {
    phase(c, Checkpoint::RequestBinding)?;
    let Selector::Declaration { name } = &raw.head else {
        return Err(error(&raw.id, "head", "assemble_map requires a view"));
    };
    let name = declaration(law, name, c, &raw.id)?;
    let Signature::View { params, .. } = &law.declarations()[&name].signature else {
        return Err(error(&raw.id, "head", "assemble_map requires a view"));
    };
    let mut arguments = BTreeMap::new();
    let mut dependencies = BTreeSet::new();
    for (key, value) in raw.arguments {
        phase(c, Checkpoint::RequestBinding)?;
        let parameter = key.strip_prefix("bind.").unwrap_or(&key);
        let name = if key == "from" || key == "to" {
            key.clone()
        } else if params.iter().any(|p| p.name == parameter) {
            format!("bind.{parameter}")
        } else {
            return Err(error(&raw.id, &key, "unknown assemble_map argument"));
        };
        if name == "from" || name == "to" {
            if !matches!(&value,Selector::Answer { path,.. } if !path.is_empty()) {
                return Err(error(&raw.id, &key, "specify a ModelAssembly Handle"));
            }
        } else if !matches!(&value, Selector::Subject { .. } | Selector::Answer { .. }) {
            return Err(error(&raw.id, &key, "specify a typed value Handle"));
        }
        if let Selector::Answer { id, .. } = &value {
            dependencies.insert(id.clone());
        }
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
                "duplicate assemble_map argument",
            )));
        }
    }
    for key in ["from".to_owned(), "to".to_owned()]
        .into_iter()
        .chain(params.iter().map(|p| format!("bind.{}", p.name)))
    {
        if !arguments.contains_key(&key) {
            return Err(invalid(problem(
                RequestIssueCode::MissingBinding,
                &raw.id,
                &key,
                "missing assemble_map argument or view binding",
            )));
        }
    }
    let r = Request {
        id: raw.id,
        text: text.into(),
        kind: QuestionKind::AssembleMap,
        head: Selector::Declaration { name },
        arguments: arguments.into_values().collect(),
        defaults: vec![],
        dependencies: dependencies.into_iter().collect(),
        constraints: vec![],
    };
    correspondence(law, &r)?;
    Ok(r)
}
pub(in crate::observed) fn shape(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    c: &Control,
) -> Result<MapAssemblyProjection, ResolveFailure> {
    let (correspondence, root) = correspondence(law, r)?;
    let reading = &law.declarations()[r.declaration().unwrap()].reading;
    let mut assemblies = Vec::new();
    for key in ["from", "to"] {
        let value = &r
            .arguments
            .iter()
            .find(|a| a.name == key)
            .ok_or_else(|| error(&r.id, key, "missing assembly"))?
            .value;
        let (plan, _) = selector_type(law, map, requests, names, value, c, (&r.id, key))?;
        let ProjectionType::ModelAssembly(a) = plan.ty else {
            return Err(error(
                &r.id,
                key,
                "assemble_map requires ModelAssembly results",
            ));
        };
        if a.root != root || &a.reading != reading {
            return Err(error(
                &r.id,
                key,
                "assembly root type or reading differs from correspondence view",
            ));
        }
        assemblies.push(a);
    }
    let target = assemblies.pop().unwrap();
    let source = assemblies.pop().unwrap();
    Ok(MapAssemblyProjection {
        source,
        target,
        correspondence: correspondence.into(),
    })
}
pub(super) fn check(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    c: &Control,
) -> Result<Vec<BindingConstraint>, ResolveFailure> {
    shape(law, map, requests, names, r, c)?;
    let Signature::View { params, .. } = &law.declarations()[r.declaration().unwrap()].signature
    else {
        unreachable!()
    };
    binding_constraints(law, map, requests, names, r, params, c)
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
    let s = shape(law, map, requests, names, r, c)?;
    let m = MapProjection {
        declaration: String::new(),
        source: s.source.root.clone(),
        target: s.target.root.clone(),
    };
    Ok(match field {
        "proposition" => ProjectionType::Proposition,
        "candidate" => ProjectionType::MapCandidate(m),
        "configuration_map" => ProjectionType::ConfigurationMap(m),
        "map" => ProjectionType::ModelMapAssembly(s),
        _ => return Err(error(&r.id, field, "assemble_map output is not public")),
    })
}
pub(super) fn project(
    law: &CheckedLaw,
    ty: &ProjectionType,
    path: &[ProjectionStep],
    c: &Control,
) -> Option<Result<(ProjectionPlan, usize), ProjectionFailure>> {
    let ProjectionType::ModelMapAssembly(s) = ty else {
        return None;
    };
    Some((|| {
        c.checkpoint(Checkpoint::Projection)?;
        let m = || MapProjection {
            declaration: String::new(),
            source: s.source.root.clone(),
            target: s.target.root.clone(),
        };
        let [ProjectionStep::Field(f), ..] = path else {
            return Err(ProjectionFailure::Invalid(
                "select a ModelMapAssembly field".into(),
            ));
        };
        let (ty, used, conditional) = match f.as_str() {
            "source" => (
                ProjectionType::ArchitectureRoot(s.source.root.clone()),
                1,
                false,
            ),
            "target" => (
                ProjectionType::ArchitectureRoot(s.target.root.clone()),
                1,
                false,
            ),
            "source_assembly" => (ProjectionType::ModelAssembly(s.source.clone()), 1, false),
            "target_assembly" => (ProjectionType::ModelAssembly(s.target.clone()), 1, false),
            "configuration_map" => (ProjectionType::ConfigurationMap(m()), 1, false),
            "correspondences" => (
                ProjectionType::Law(Type::Set(Box::new(Type::Ref(s.correspondence.clone())))),
                1,
                false,
            ),
            "locals" => {
                let [_, ProjectionStep::Index(_), ProjectionStep::Field(f), ..] = path else {
                    return Err(ProjectionFailure::Invalid(
                        "select a local map field".into(),
                    ));
                };
                (
                    match f.as_str() {
                        "correspondence" => {
                            ProjectionType::Law(Type::Ref(s.correspondence.clone()))
                        }
                        "source" => ProjectionType::ArchitectureRoot(s.source.root.clone()),
                        "target" => ProjectionType::ArchitectureRoot(s.target.root.clone()),
                        "map" | "restriction" => ProjectionType::ConfigurationMap(m()),
                        "proposition" => ProjectionType::Proposition,
                        _ => {
                            return Err(ProjectionFailure::Invalid(
                                "local map field is not public".into(),
                            ));
                        }
                    },
                    3,
                    true,
                )
            }
            "generators" | "laws" => {
                let [
                    _,
                    ProjectionStep::Index(_),
                    ProjectionStep::Field(field),
                    ..,
                ] = path
                else {
                    return Err(ProjectionFailure::Invalid(
                        "select a transport row field".into(),
                    ));
                };
                let ty = if field == "proposition" {
                    ProjectionType::Proposition
                } else if f == "laws" && matches!(field.as_str(), "source_law" | "target_law") {
                    ProjectionType::LawInstance
                } else {
                    let source = matches!(field.as_str(), "source" | "source_object");
                    let target = matches!(field.as_str(), "target" | "target_object");
                    if !source && !target
                        || (f == "generators" && !matches!(field.as_str(), "source" | "target"))
                        || (f == "laws"
                            && !matches!(field.as_str(), "source_object" | "target_object"))
                    {
                        return Err(ProjectionFailure::Invalid(
                            "transport row field is not public".into(),
                        ));
                    }
                    let shape = if source { &s.source } else { &s.target };
                    let namespaces = crate::construction::reading_namespaces(
                        law,
                        &shape.reading,
                        c,
                    )
                    .map_err(|e| match e {
                        crate::construction::ConstructionFailure::Stopped(s) => {
                            ProjectionFailure::Interrupted(s)
                        }
                        _ => ProjectionFailure::Invalid("transport reading is unavailable".into()),
                    })?;
                    let mut options = Vec::new();
                    for d in law.definitions().declarations().values() {
                        c.checkpoint(Checkpoint::Projection)?;
                        if !namespaces.contains(&d.namespace) {
                            continue;
                        }
                        match &d.signature {
                            archsig_input::definition::PrimitiveSignature::Arrow {
                                owner,
                                endpoint,
                                ..
                            } if f == "generators" && owner == &shape.root => {
                                options.push(ProjectionType::Operation(MapProjection {
                                    declaration: d.name.clone(),
                                    source: endpoint.clone(),
                                    target: endpoint.clone(),
                                }))
                            }
                            archsig_input::definition::PrimitiveSignature::Entity {
                                owner, ..
                            } if f == "laws"
                                && (d.name == shape.root
                                    || owner.as_deref() == Some(shape.root.as_str())) =>
                            {
                                options.push(ProjectionType::ObjectComponentRoot(d.name.clone()))
                            }
                            _ => {}
                        }
                    }
                    if options.is_empty() {
                        return Err(ProjectionFailure::Invalid(
                            "transport row type is unavailable".into(),
                        ));
                    }
                    if options.len() == 1 {
                        options.pop().unwrap()
                    } else {
                        ProjectionType::Dynamic(options)
                    }
                };
                (ty, 3, true)
            }
            _ => {
                return Err(ProjectionFailure::Invalid(
                    "ModelMapAssembly field is not public".into(),
                ));
            }
        };
        Ok((ProjectionPlan { ty, conditional }, used))
    })())
}
