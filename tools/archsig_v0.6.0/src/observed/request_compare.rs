//! 固定compare署名と、語/作用を比較する元値の静的型を解決する。
use super::composition::Shape;
use super::*;
fn error(r: &str, key: &str, message: &str) -> ResolveFailure {
    invalid(problem(RequestIssueCode::Type, r, key, message))
}
pub(in crate::observed) fn kind(request: &Request) -> Result<&str, ResolveFailure> {
    match request
        .arguments
        .iter()
        .find(|a| a.name == "kind")
        .map(|a| &a.value)
    {
        Some(Selector::Enum { value }) => Ok(value),
        _ => Err(error(&request.id, "kind", "compareのkindが必要")),
    }
}
pub(super) fn resolve(
    raw: RawRequest,
    text: &str,
    control: &mut Control,
) -> Result<Request, ResolveFailure> {
    let mut arguments = Vec::new();
    let mut dependencies = BTreeSet::new();
    for (key, mut value) in raw.arguments {
        phase(control, Checkpoint::RequestBinding)?;
        if !matches!(key.as_str(), "to" | "kind" | "along") {
            return Err(error(&raw.id, &key, "compareの固定引数はto/kind/along"));
        }
        if key == "kind" {
            let Selector::Declaration { name } = value else {
                return Err(error(&raw.id, &key, "compareのkindは固定語を指定する"));
            };
            if !matches!(
                name.as_str(),
                "value" | "word" | "action" | "relation" | "diagnostics"
            ) {
                return Err(error(&raw.id, &key, "compareの未知kind"));
            }
            value = Selector::Enum { value: name };
        }
        arguments.push(RequestArgument {
            name: key,
            value,
            origin: ArgumentOrigin::Explicit,
        });
    }
    let request = Request {
        id: raw.id,
        text: text.into(),
        kind: QuestionKind::Compare,
        head: raw.head,
        arguments,
        defaults: vec![],
        dependencies: vec![],
        constraints: vec![],
    };
    let mode = kind(&request)?;
    let to = request
        .arguments
        .iter()
        .find(|a| a.name == "to")
        .ok_or_else(|| error(&request.id, "to", "compareのtoが必要"))?;
    let along = request.arguments.iter().find(|a| a.name == "along");
    if (mode == "diagnostics") != along.is_some() {
        return Err(error(&request.id, "along", "alongはdiagnosticsだけで必須"));
    }
    for (key, selector) in std::iter::once(("head", &request.head))
        .chain(std::iter::once(("to", &to.value)))
        .chain(along.map(|a| ("along", &a.value)))
    {
        match selector {
            Selector::Answer { id, path } if !path.is_empty() => {
                dependencies.insert(id.clone());
            }
            Selector::Subject { .. } if mode == "value" && key != "along" => {}
            _ => {
                return Err(error(
                    &request.id,
                    key,
                    "compareは型付きHandleを出力fieldまで指定する",
                ))
            }
        }
    }
    Ok(Request {
        dependencies: dependencies.into_iter().collect(),
        ..request
    })
}
pub(super) fn constraints(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    request: &Request,
    control: &mut Control,
) -> Result<Vec<BindingConstraint>, ResolveFailure> {
    let mode = kind(request)?;
    if !matches!(mode, "word" | "action") {
        return Err(ResolveFailure::NotApplicable {
            request: request.id.clone(),
            kind: "compare".into(),
            architecture_environment: false,
        });
    }
    let to = &request
        .arguments
        .iter()
        .find(|a| a.name == "to")
        .ok_or_else(|| error(&request.id, "to", "toがない"))?
        .value;
    let left = composition::selected(
        law,
        map,
        requests,
        names,
        &request.head,
        request,
        "head",
        control,
    )?;
    let right = composition::selected(law, map, requests, names, to, request, "to", control)?;
    match (&left, &right) {
        (Shape::Path(a, b), Shape::Path(c, d)) => {
            if mode == "action" && (a != c || b != d) {
                return Err(error(&request.id, "to", "作用比較のPathの始終型が違う"));
            }
        }
        (Shape::Operation(a), Shape::Operation(b)) => {
            if mode == "action"
                && (a.source != b.source
                    || a.target != b.target
                    || a.reading != b.reading
                    || a.to_reading != b.to_reading)
            {
                return Err(error(
                    &request.id,
                    "to",
                    "作用比較のOperationの始終型・readingが違う",
                ));
            }
        }
        _ => {
            return Err(error(
                &request.id,
                "to",
                "OperationとPathを混在して比較できない",
            ))
        }
    }
    if matches!(left, Shape::Operation(_)) {
        return Ok(vec![]);
    }
    let mut out = vec![];
    for (key, selector) in [("head", &request.head), ("to", to)] {
        let (plan, owners) = selector_type(
            law,
            map,
            requests,
            names,
            selector,
            control,
            (&request.id, key),
        )?;
        let ProjectionType::Law(expected @ Type::Path(..)) = &plan.ty else {
            return Err(error(&request.id, key, "Pathの参照型がない"));
        };
        out.push(BindingConstraint {
            parameter: key.into(),
            expected: expected.clone(),
            selector: selector.clone(),
            projection: plan.clone(),
            owner: None,
            projection_owners: owners,
            expected_owners: BTreeMap::new(),
            dynamic: plan.conditional,
        });
    }
    Ok(out)
}
pub(super) fn output_type(
    request: &Request,
    field: &str,
) -> Result<ProjectionType, ResolveFailure> {
    match field {
        "comparison" => Ok(ProjectionType::Comparison),
        "proposition" => Ok(ProjectionType::Proposition),
        _ => Err(error(&request.id, field, "compareの非公開出力")),
    }
}
