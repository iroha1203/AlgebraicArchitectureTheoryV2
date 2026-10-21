//! 固定compose署名と、値を実行しないOperation/Pathの型解決。
use super::*;
use crate::observed::projection::OperationProjection;
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Shape {
    Operation(OperationProjection),
    Path(String, String),
}
fn error(r: &str, key: &str, message: &str) -> ResolveFailure {
    invalid(problem(RequestIssueCode::Type, r, key, message))
}
pub(super) fn resolve(
    raw: RawRequest,
    text: &str,
    control: &mut Control,
) -> Result<Request, ResolveFailure> {
    phase(control, Checkpoint::RequestBinding)?;
    let mut dependencies = BTreeSet::new();
    let mut arguments = Vec::new();
    for (key, value) in raw.arguments {
        phase(control, Checkpoint::RequestBinding)?;
        if key != "then" {
            return Err(error(&raw.id, &key, "composeの固定引数はthenだけ"));
        }
        arguments.push(RequestArgument {
            name: key,
            value,
            origin: ArgumentOrigin::Explicit,
        });
    }
    if arguments.len() != 1 {
        return Err(error(&raw.id, "then", "composeのthenが必要"));
    }
    for (key, value) in [("head", &raw.head), ("then", &arguments[0].value)] {
        let Selector::Answer { id, path } = value else {
            return Err(error(
                &raw.id,
                key,
                "composeは結果のOperationまたはPathを指定する",
            ));
        };
        if path.is_empty() {
            return Err(error(&raw.id, key, "composeは出力fieldまで指定する"));
        }
        dependencies.insert(id.clone());
    }
    Ok(Request {
        id: raw.id,
        text: text.into(),
        kind: QuestionKind::Compose,
        head: raw.head,
        arguments,
        dependencies: dependencies.into_iter().collect(),
        defaults: vec![],
        constraints: vec![],
    })
}
fn reading(r: &Request, key: &str) -> Result<String, ResolveFailure> {
    match r.arguments.iter().find(|a| a.name == key).map(|a| &a.value) {
        Some(Selector::Declaration { name }) => Ok(name.clone()),
        _ => Err(error(&r.id, key, "mapの解決済みreadingがない")),
    }
}
fn selected(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    value: &Selector,
    request: &Request,
    key: &str,
    control: &mut Control,
) -> Result<Shape, ResolveFailure> {
    let (plan, _) = selector_type(
        law,
        map,
        requests,
        names,
        value,
        control,
        (&request.id, key),
    )?;
    match plan.ty {
        ProjectionType::Operation(s) => {
            let Selector::Answer { id, .. } = value else {
                return Err(error(&request.id, key, "Operationの元要求がない"));
            };
            let producer = &requests[names[id]];
            Ok(Shape::Operation(OperationProjection {
                source: s.source,
                target: s.target,
                reading: reading(producer, "reading")?,
                to_reading: reading(producer, "to_reading")?,
                word: vec![s.declaration],
            }))
        }
        ProjectionType::ComposedOperation(s) => Ok(Shape::Operation(s)),
        ProjectionType::Law(Type::Path(ref a, ref b)) => Ok(Shape::Path(a.clone(), b.clone())),
        _ => Err(error(
            &request.id,
            key,
            "composeは二つのOperationまたは二つのPathを要求する",
        )),
    }
}
pub(super) fn shape(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    request: &Request,
    control: &mut Control,
) -> Result<Shape, ResolveFailure> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        phase(control, Checkpoint::RequestBinding)?;
        let then = request
            .arguments
            .iter()
            .find(|a| a.name == "then")
            .ok_or_else(|| error(&request.id, "then", "thenがない"))?;
        let left = selected(
            law,
            map,
            requests,
            names,
            &request.head,
            request,
            "head",
            control,
        )?;
        let right = selected(
            law,
            map,
            requests,
            names,
            &then.value,
            request,
            "then",
            control,
        )?;
        match (left, right) {
            (Shape::Operation(mut a), Shape::Operation(b))
                if a.target == b.source && a.to_reading == b.reading =>
            {
                a.target = b.target;
                a.to_reading = b.to_reading;
                for word in b.word {
                    phase(control, Checkpoint::RequestBinding)?;
                    a.word.push(word);
                }
                Ok(Shape::Operation(a))
            }
            (Shape::Path(a, b), Shape::Path(c, d)) if b == c => Ok(Shape::Path(a, d)),
            _ => Err(error(
                &request.id,
                "then",
                "composeの型・reading・中間型が合わない（OperationとPathの混在も不可）",
            )),
        }
    })
}
pub(super) fn output_type(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    request: &Request,
    field: &str,
    control: &mut Control,
) -> Result<ProjectionType, ResolveFailure> {
    let shape = shape(law, map, requests, names, request, control)?;
    match (field, shape) {
        ("proposition", _) => Ok(ProjectionType::Proposition),
        ("operation", Shape::Operation(s)) => Ok(ProjectionType::ComposedOperation(s)),
        ("map", Shape::Operation(s)) => Ok(ProjectionType::ComposedMap(s)),
        ("operation", Shape::Path(a, b)) => Ok(ProjectionType::Law(Type::Path(a, b))),
        _ => Err(error(&request.id, field, "composeの非公開出力")),
    }
}

pub(super) fn constraints(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    request: &Request,
    control: &mut Control,
) -> Result<Vec<BindingConstraint>, ResolveFailure> {
    if !matches!(
        shape(law, map, requests, names, request, control)?,
        Shape::Path(..)
    ) {
        return Ok(vec![]);
    }
    let then = request
        .arguments
        .iter()
        .find(|a| a.name == "then")
        .ok_or_else(|| error(&request.id, "then", "thenがない"))?;
    let mut out = vec![];
    for (key, selector) in [("head", &request.head), ("then", &then.value)] {
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
