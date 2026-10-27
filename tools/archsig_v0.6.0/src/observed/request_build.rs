//! buildの固定署名、reading、原始rootと公開結果Handleを解決する。
use super::*;
use crate::{
    construction::{ConstructionFailure, reading_namespaces},
    definition::PrimitiveSignature,
};

fn error(request: &str, argument: &str, message: &str) -> ResolveFailure {
    invalid(problem(RequestIssueCode::Type, request, argument, message))
}
fn namespaces(
    law: &CheckedLaw,
    reading: &str,
    id: &str,
    c: &mut Control,
) -> Result<BTreeSet<String>, ResolveFailure> {
    reading_namespaces(law, reading, c).map_err(|failure| match failure {
        ConstructionFailure::Stopped(reason) => stopped(reason),
        other => error(
            id,
            "head",
            &format!("incompatible build reading: {other:?}"),
        ),
    })
}
pub(super) fn resolve(
    law: &CheckedLaw,
    raw: RawRequest,
    text: &str,
    c: &mut Control,
) -> Result<Request, ResolveFailure> {
    phase(c, Checkpoint::RequestBinding)?;
    let Selector::Declaration { name } = &raw.head else {
        return Err(error(&raw.id, "head", "build head must be a fully qualified reading name"));
    };
    namespaces(law, name, &raw.id, c)?;
    let mut dependencies = vec![];
    let mut arguments = vec![];
    for (key, value) in raw.arguments {
        phase(c, Checkpoint::RequestBinding)?;
        if key != "on" {
            return Err(error(&raw.id, &key, "build only accepts the fixed argument on"));
        }
        match &value {
            Selector::Subject { .. } => {}
            Selector::Answer { id, path } if !path.is_empty() => dependencies.push(id.clone()),
            _ => {
                return Err(error(
                    &raw.id,
                    &key,
                    "build on must be a primitive root reference or a Handle with an output field",
                ));
            }
        }
        arguments.push(RequestArgument {
            name: key,
            value,
            origin: ArgumentOrigin::Explicit,
        });
    }
    if arguments.len() != 1 {
        return Err(error(&raw.id, "on", "build requires on"));
    }
    Ok(Request {
        id: raw.id,
        text: text.into(),
        kind: QuestionKind::Build,
        head: raw.head,
        arguments,
        defaults: vec![],
        dependencies,
        constraints: vec![],
    })
}
fn roots(
    law: &CheckedLaw,
    ty: &ProjectionType,
    visible: &BTreeSet<String>,
    c: &mut Control,
    found: &mut BTreeSet<String>,
    architecture: bool,
) -> Result<(), ResolveFailure> {
    phase(c, Checkpoint::RequestBinding)?;
    match ty {
        ProjectionType::ArchitectureRoot(_) if !architecture => {},
        ProjectionType::Law(Type::Ref(name)) | ProjectionType::ArchitectureRoot(name) => {
            if let Some(declaration) = law.definitions.declarations.get(name) {
                if visible.contains(&declaration.namespace)
                    && matches!(
                        declaration.signature,
                        PrimitiveSignature::Entity { owner: None, .. }
                    )
                {
                    found.insert(name.clone());
                }
            }
        }
        ProjectionType::Dynamic(options) => {
            for option in options {
                roots(law, option, visible, c, found,architecture)?;
            }
        }
        _ => {}
    }
    Ok(())
}
pub(super) fn root_types(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    c: &mut Control,
) -> Result<BTreeSet<String>, ResolveFailure> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        phase(c, Checkpoint::RequestBinding)?;
        let Selector::Declaration { name: reading } = &r.head else {
            return Err(error(&r.id, "head", "missing build reading"));
        };
        let visible = namespaces(law, reading, &r.id, c)?;
        let on = r
            .arguments
            .iter()
            .find(|a| a.name == "on")
            .ok_or_else(|| error(&r.id, "on", "missing build on"))?;
        let (plan, _) = selector_type(law, map, requests, names, &on.value, c, (&r.id, "on"))?;
        let mut found = BTreeSet::new();
        roots(law, &plan.ty, &visible, c, &mut found,matches!(r.kind,QuestionKind::Solve|QuestionKind::Repair))?;
        if found.is_empty() {
            return Err(error(
                &r.id,
                "on",
                "build on must reference an entity without an owner in the reading vocabulary",
            ));
        }
        Ok(found)
    })
}
pub(super) fn check_on(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    c: &mut Control,
) -> Result<(), ResolveFailure> {
    root_types(law, map, requests, names, r, c).map(|_| ())
}
pub(super) fn output_type(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    field: &str,
    c: &mut Control,
) -> Result<ProjectionType, ResolveFailure> {
    if field == "proposition" {
        return Ok(ProjectionType::Proposition);
    }
    if !matches!(field, "object" | "algebra") {
        return Err(error(&r.id, field, "build output is not public"));
    }
    let types = root_types(law, map, requests, names, r, c)?
        .into_iter()
        .map(|name| {
            if field == "object" {
                ProjectionType::ArchitectureRoot(name)
            } else {
                ProjectionType::ObjectAlgebraRoot(name)
            }
        })
        .collect::<Vec<_>>();
    Ok(if types.len() == 1 {
        types.into_iter().next().expect("root型が一つ")
    } else {
        ProjectionType::Dynamic(types)
    })
}

#[cfg(test)]
#[path = "request_build_tests.rs"]
mod tests;
