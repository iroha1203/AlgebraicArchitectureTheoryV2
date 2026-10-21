//! 固定compare署名と、値/語/作用を比較する元値の静的型を解決する。
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
    arguments.sort_by(|a, b| a.name.cmp(&b.name));
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
    if mode == "value" {
        return value_constraints(law, map, requests, names, request, control);
    }
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

fn value_constraints(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    request: &Request,
    control: &mut Control,
) -> Result<Vec<BindingConstraint>, ResolveFailure> {
    let to = &request
        .arguments
        .iter()
        .find(|a| a.name == "to")
        .ok_or_else(|| error(&request.id, "to", "toがない"))?
        .value;
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
        let ProjectionType::Law(ty) = &plan.ty else {
            return Err(error(
                &request.id,
                key,
                "value比較には同じ原始型Pの値が必要",
            ));
        };
        let expected = ty
            .erase_controlled::<super::super::control::CheckFailure<Box<crate::issue::Issue>>>(
                control,
                Checkpoint::RequestBinding,
            )
            .map_err(|e| match e {
                super::super::control::CheckFailure::Stopped(s) => stopped(s),
                super::super::control::CheckFailure::Input(_) => {
                    error(&request.id, key, "原始型の解決に失敗した")
                }
            })?;
        if out
            .first()
            .is_some_and(|c: &BindingConstraint| c.expected != expected)
        {
            return Err(error(&request.id, key, "value比較の原始型Pが違う"));
        }
        out.push(BindingConstraint {
            parameter: key.into(),
            expected,
            selector: selector.clone(),
            projection: plan.clone(),
            owner: None,
            projection_owners: owners,
            expected_owners: BTreeMap::new(),
            dynamic: plan.conditional,
        });
    }
    for constraint in &out {
        if !ground_type(&constraint.expected, law, control, &mut BTreeSet::new())? {
            if super::super::term::contains(&constraint.expected, law, control).map_err(
                |e| match e {
                    super::super::result::ValidationFailure::Stop(s) => stopped(s),
                    _ => error(&request.id, &constraint.parameter, "原始型の定義が違う"),
                },
            )? {
                return Err(ResolveFailure::NotApplicable {
                    request: request.id.clone(),
                    kind: "compare".into(),
                    architecture_environment: false,
                });
            }
            return Err(error(
                &request.id,
                &constraint.parameter,
                "value比較には原始型Pの値が必要",
            ));
        }
    }
    Ok(out)
}
fn ground_type(
    ty: &Type,
    law: &CheckedLaw,
    control: &mut Control,
    active: &mut BTreeSet<String>,
) -> Result<bool, ResolveFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        phase(control, Checkpoint::RequestBinding)?;
        Ok(match ty {
            Type::Unit
            | Type::Bool
            | Type::Z
            | Type::Q
            | Type::Fp(_)
            | Type::Text
            | Type::Ref(_) => true,
            Type::Tuple(v) => {
                for t in v {
                    if !ground_type(t, law, control, active)? {
                        return Ok(false);
                    }
                }
                true
            }
            Type::List(t) | Type::Set(t) | Type::Option(t) => ground_type(t, law, control, active)?,
            Type::Map(a, b) => matches!((a.as_ref(), b.as_ref()), (Type::Ref(_), Type::Ref(_))),
            Type::Data(family) => {
                if !active.insert(family.clone()) {
                    return Ok(true);
                }
                let ctors = super::super::data::constructors(law, family)
                    .map_err(|_| error("", family, "Dataの定義がない"))?;
                let mut ground = true;
                for ctor in ctors {
                    for t in &ctor.arguments {
                        ground &= ground_type(t, law, control, active)?;
                    }
                }
                active.remove(family);
                ground
            }
            _ => false,
        })
    })
}
