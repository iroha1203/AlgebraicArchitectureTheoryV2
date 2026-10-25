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
    if mode == "diagnostics" {
        return diagnostic_constraints(law, map, requests, names, request, control);
    }
    if !matches!(mode, "word" | "action" | "relation") {
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
            if matches!(mode, "action" | "relation") && (a != c || b != d) {
                return Err(error(&request.id, "to", "作用比較のPathの始終型が違う"));
            }
        }
        (Shape::Operation(a), Shape::Operation(b)) => {
            if mode == "relation" {
                return Err(ResolveFailure::NotApplicable { request: request.id.clone(), kind: "compare".into(), architecture_environment: false });
            }
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
    let mut plans = vec![];
    for (key,selector) in [("head",&request.head),("to",to)] {
        let (plan,owners) = selector_type(law,map,requests,names,selector,control,(&request.id,key))?;
        plans.push((key,selector,plan,owners));
    }
    if plans.iter().all(|(_,_,plan,_)|plan.ty==ProjectionType::Vector) {
        // Moduleの同一性は実際の型付き出力で構成条件として検査する。
        return Ok(vec![]);
    }
    let mut selections = vec![];
    for (key,selector,plan,owners) in plans {
        let mut types = vec![];
        value_types(&plan.ty, control, &mut types)?;
        if types.is_empty() {
            return Err(error(
                &request.id,
                key,
                "value比較には同じ原始型Pの値が必要",
            ));
        }
        selections.push((key, selector, plan, owners, types));
    }
    let mut common = vec![];
    for left in &selections[0].4 {
        for right in &selections[1].4 {
            phase(control, Checkpoint::RequestBinding)?;
            if left == right {
                common.push(left.clone());
                break;
            }
        }
    }
    if common.is_empty() {
        return Err(error(&request.id, "to", "value比較の原始型Pが違う"));
    }
    let mut out = vec![];
    for (key, selector, plan, owners, _) in selections {
        // value比較には消費側parameter型がない。共通候補は同parameterの選択肢として
        // 保ち、現在の射影値を選んだ後に一候補への適合と左右の同型を検査する。
        for expected in &common {
            phase(control, Checkpoint::RequestBinding)?;
            out.push(BindingConstraint {
                parameter: key.into(),
                expected: expected.clone(),
                selector: selector.clone(),
                projection: plan.clone(),
                owner: None,
                projection_owners: owners.clone(),
                expected_owners: BTreeMap::new(),
                dynamic: plan.conditional || matches!(plan.ty, ProjectionType::Dynamic(_)),
            });
        }
    }
    Ok(out)
}
fn value_types(
    projection: &ProjectionType,
    control: &mut Control,
    out: &mut Vec<Type>,
) -> Result<(), ResolveFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        phase(control, Checkpoint::RequestBinding)?;
        match projection {
            ProjectionType::Dynamic(candidates) => {
                for candidate in candidates {
                    value_types(candidate, control, out)?;
                }
            }
            ProjectionType::Law(ty) => {
                let ty=ty.erase_controlled::<super::super::control::CheckFailure<Box<crate::issue::Issue>>>(control,Checkpoint::RequestBinding)
                    .map_err(|e|match e {super::super::control::CheckFailure::Stopped(s)=>stopped(s),
                        super::super::control::CheckFailure::Input(_)=>error("","type","原始型の解決に失敗した")})?;
                if super::super::data::primitive_type(&ty, control).map_err(|e| match e {
                    super::super::result::ValidationFailure::Stop(s) => stopped(s),
                    _ => error("", "type", "原始型の定義が違う"),
                })? {
                    let mut duplicate = false;
                    for existing in out.iter() {
                        phase(control, Checkpoint::RequestBinding)?;
                        duplicate |= existing == &ty;
                    }
                    if !duplicate {
                        out.push(ty);
                    }
                }
            }
            _ => {}
        }
        Ok(())
    })
}

// アフィン局所系の係数は、localize が選ぶ change の parameter 型から決まる。
// 有限診断にはここで係数環を仮定しない。
fn diagnostic_coefficient(
    law: &CheckedLaw, requests: &[Request], names: &BTreeMap<String, usize>,
    diagnose: &Request, c: &mut Control,
) -> Result<Option<Type>, ResolveFailure> {
    phase(c, Checkpoint::RequestBinding)?;
    let Selector::Answer { id, .. } = &diagnose.head else { return Ok(None); };
    let Some(localize) = names.get(id).and_then(|i| requests.get(*i)) else { return Ok(None); };
    if localize.kind != QuestionKind::Localize { return Ok(None); }
    let Some(Selector::Declaration { name }) = localize.arguments.iter()
        .find(|a| a.name == "using").map(|a| &a.value) else { return Ok(None); };
    let Some(declaration) = law.declarations.get(name) else { return Ok(None); };
    let Signature::Change { params, .. } = &declaration.signature else { return Ok(None); };
    for coefficient in [Type::Z, Type::Q] {
        for parameter in params.iter().skip(1) {
            phase(c, Checkpoint::RequestBinding)?;
            if parameter.ty == coefficient { return Ok(Some(coefficient)); }
        }
    }
    Ok(None)
}

fn diagnostic_constraints(
    law: &CheckedLaw, map: &CheckedArchMap, requests: &[Request],
    names: &BTreeMap<String, usize>, r: &Request, c: &mut Control,
) -> Result<Vec<BindingConstraint>, ResolveFailure> {
    let to = &r.arguments.iter().find(|a|a.name=="to").ok_or_else(||error(&r.id,"to","toがない"))?.value;
    let along = &r.arguments.iter().find(|a|a.name=="along").ok_or_else(||error(&r.id,"along","alongがない"))?.value;
    let mut shapes = vec![];
    let mut coefficients = vec![];
    for (key,selector) in [("head",&r.head),("to",to)] {
        let (plan,_) = selector_type(law,map,requests,names,selector,c,(&r.id,key))?;
        if plan.ty != ProjectionType::Diagnostic { return Err(error(&r.id,key,"診断比較の対象はDiagnostic")); }
        let Selector::Answer{id,..}=selector else{return Err(error(&r.id,key,"診断の元要求がない"))};
        let producer=&requests[*names.get(id).ok_or_else(||error(&r.id,key,"診断の元要求がない"))?];
        let degree=producer.arguments.iter().find(|a|a.name=="degree").map(|a|a.value.clone());
        let side=producer.arguments.iter().find(|a|a.name=="side").map(|a|a.value.clone());
        if producer.kind!=QuestionKind::Diagnose || degree.is_none() || side.is_none() {return Err(error(&r.id,key,"診断の次数・sideがない"));}
        coefficients.push(diagnostic_coefficient(law, requests, names, producer, c)?);
        shapes.push((degree,side));
    }
    if shapes[0]!=shapes[1] {return Err(error(&r.id,"to","診断比較のdegree/sideが異なる"));}
    if matches!((&coefficients[0], &coefficients[1]), (Some(a), Some(b)) if a != b) {
        return Err(error(&r.id, "to", "診断比較の係数環が異なる"));
    }
    let operation=composition::selected(law,map,requests,names,along,r,"along",c)?;
    if !matches!(operation,Shape::Operation(_)) {return Err(error(&r.id,"along","alongは確認済みOperationを指定する"));}
    Ok(vec![])
}
