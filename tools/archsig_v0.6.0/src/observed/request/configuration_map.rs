//! 原始correspondenceの公開map要求の選択・型・readingを解決する。
use super::*;
use crate::observed::projection::MapProjection;
use crate::{
    construction::{ConstructionFailure, reading_namespaces},
    definition::PrimitiveSignature,
};

fn error(id: &str, argument: &str, message: &str) -> ResolveFailure {
    invalid(problem(RequestIssueCode::Type, id, argument, message))
}
fn shape(
    law: &CheckedLaw,
    name: &str,
    id: &str,
    control: &mut Control,
) -> Result<MapProjection, ResolveFailure> {
    phase(control, Checkpoint::RequestBinding)?;
    let d = law
        .definitions()
        .declarations()
        .get(name)
        .ok_or_else(|| error(id, "head", "missing correspondence declaration"))?;
    let PrimitiveSignature::Correspondence { from, to, .. } = &d.signature else {
        return Err(error(id, "head", "map requires a primitive correspondence declaration"));
    };
    Ok(MapProjection {
        declaration: name.into(),
        source: from.clone(),
        target: to.clone(),
    })
}
fn namespaces(
    law: &CheckedLaw,
    reading: &str,
    id: &str,
    key: &str,
    control: &mut Control,
) -> Result<BTreeSet<String>, ResolveFailure> {
    reading_namespaces(law, reading, control).map_err(|e| match e {
        ConstructionFailure::Stopped(r) => stopped(r),
        e => error(id, key, &format!("{e:?}")),
    })
}
pub(super) fn resolve(
    law: &CheckedLaw,
    raw: RawRequest,
    text: &str,
    control: &mut Control,
) -> Result<Request, ResolveFailure> {
    let Selector::Declaration { name } = &raw.head else {
        return Err(error(&raw.id, "head", "map head must be a correspondence declaration"));
    };
    let mut found = Vec::new();
    for (candidate, d) in law.definitions().declarations() {
        phase(control, Checkpoint::RequestBinding)?;
        if candidate == name
            || (!name.contains('.') && law.resolved_names().get(candidate).is_some_and(|parts| parts.short() == name))
        {
            found.push((candidate, d));
        }
    }
    if found.len() != 1 {
        return Err(error(
            &raw.id,
            "head",
            "correspondence declaration name does not exist or is ambiguous",
        ));
    }
    let name = found[0].0.clone();
    let signature = shape(law, &name, &raw.id, control)?;
    let mut args = BTreeMap::new();
    for (key, value) in raw.arguments {
        phase(control, Checkpoint::RequestBinding)?;
        if !matches!(key.as_str(), "on" | "reading" | "to_reading" | "kind") {
            return Err(error(&raw.id, &key, "unknown map argument"));
        }
        args.insert(
            key.clone(),
            RequestArgument {
                name: key,
                value,
                origin: ArgumentOrigin::Explicit,
            },
        );
    }
    let on = args
        .get("on")
        .ok_or_else(|| error(&raw.id, "on", "map requires on"))?;
    if !matches!(on.value, Selector::Subject { .. } | Selector::Answer { .. }) {
        return Err(error(&raw.id, "on", "on must be a correspondence instance Handle"));
    }
    let mut dependencies = vec![];
    if let Selector::Answer { id, path } = &on.value {
        if path.is_empty() {
            return Err(error(&raw.id, "on", "specify an output field"));
        }
        dependencies.push(id.clone());
    }
    let Selector::Declaration { name: reading } = &args
        .get("reading")
        .ok_or_else(|| error(&raw.id, "reading", "map requires reading"))?
        .value
    else {
        return Err(error(&raw.id, "reading", "specify a fully qualified reading name"));
    };
    let reading = reading.clone();
    args.entry("to_reading".into())
        .or_insert_with(|| RequestArgument {
            name: "to_reading".into(),
            value: Selector::Declaration {
                name: reading.clone(),
            },
            origin: ArgumentOrigin::Defaulted,
        });
    args.entry("kind".into())
        .or_insert_with(|| RequestArgument {
            name: "kind".into(),
            value: Selector::Declaration {
                name: "configuration".into(),
            },
            origin: ArgumentOrigin::Defaulted,
        });
    let Selector::Declaration { name: to } = &args["to_reading"].value else {
        return Err(error(&raw.id, "to_reading", "specify a fully qualified to_reading name"));
    };
    for (key, r, ty) in [
        ("reading", reading.as_str(), signature.source.as_str()),
        ("to_reading", to.as_str(), signature.target.as_str()),
    ] {
        let imported = namespaces(law, r, &raw.id, key, control)?;
        let d = &law.definitions().declarations()[ty];
        if !imported.contains(&d.namespace) {
            return Err(error(
                &raw.id,
                key,
                "reading vocabulary does not contain the correspondence root types",
            ));
        }
    }
    let Selector::Declaration { name: kind } = &args["kind"].value else {
        return Err(error(
            &raw.id,
            "kind",
            "map kind must be configuration or object_algebra",
        ));
    };
    if !matches!(kind.as_str(), "configuration" | "object_algebra") {
        return Err(error(
            &raw.id,
            "kind",
            "map kind must be configuration or object_algebra",
        ));
    }
    let kind = kind.clone();
    let selected = args
        .get_mut("kind")
        .ok_or_else(|| error(&raw.id, "kind", "missing resolved kind"))?;
    selected.value = Selector::Enum { value: kind };
    phase(control, Checkpoint::RequestBinding)?;
    Ok(Request {
        id: raw.id,
        text: text.into(),
        kind: QuestionKind::Map,
        head: Selector::Declaration { name },
        arguments: args.into_values().collect(),
        defaults: vec![],
        dependencies,
        constraints: vec![],
    })
}
pub(super) fn output_type(
    law: &CheckedLaw,
    r: &Request,
    field: &str,
    control: &mut Control,
) -> Result<ProjectionType, ResolveFailure> {
    let Selector::Declaration { name } = &r.head else {
        return Err(error(&r.id, "head", "map head is not a declaration"));
    };
    let s = shape(law, name, &r.id, control)?;
    match field {
        "candidate" => Ok(ProjectionType::MapCandidate(s)),
        "map"
            if r.arguments.iter().any(|a| {
                a.name == "kind"
                    && matches!(&a.value,Selector::Enum {value} if value=="object_algebra")
            }) =>
        {
            Ok(ProjectionType::ObjectAlgebraMap(s))
        }
        "map" => Ok(ProjectionType::ConfigurationMap(s)),
        "operation" => Ok(ProjectionType::Operation(s)),
        "proposition" => Ok(ProjectionType::Proposition),
        _ => Err(error(&r.id, field, "map output is not public")),
    }
}
pub(super) fn constraints(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    r: &Request,
    control: &mut Control,
) -> Result<Vec<BindingConstraint>, ResolveFailure> {
    let Selector::Declaration { name } = &r.head else {
        return Err(error(&r.id, "head", "map head is not a declaration"));
    };
    let on = r
        .arguments
        .iter()
        .find(|a| a.name == "on")
        .ok_or_else(|| error(&r.id, "on", "missing on"))?;
    let (plan, projection_owners) =
        selector_type(law, map, requests, names, &on.value, control, (&r.id, "on"))?;
    let ty = Type::Ref(name.clone());
    if !projection::can_bind_controlled(&plan.ty, &ty, control).map_err(stopped)? {
        return Err(error(&r.id, "on", "on type does not match the correspondence declaration"));
    }
    let dynamic = plan.conditional || matches!(plan.ty, ProjectionType::Dynamic(_));
    Ok(vec![BindingConstraint {
        parameter: "on".into(),
        expected: ty,
        selector: on.value.clone(),
        projection: plan,
        owner: None,
        projection_owners,
        expected_owners: BTreeMap::new(),
        dynamic,
    }])
}
