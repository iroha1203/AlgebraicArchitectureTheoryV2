//! 局所診断を、指定されたOperationの実作用に沿って比較する。
use super::*;
use crate::observed::public_compose;
#[path = "local_finite_transport.rs"]
mod finite_transport;
#[path = "local_integer_compare.rs"]
mod integer;
#[path = "local_rational_compare.rs"]
mod rational;
fn local(g: &Graph, r: NodeRef) -> Result<&Data, ValidationFailure> {
    match &g.get(r)?.payload {
        Some(Payload::Construction(v)) => match &v.data {
            D::Local(d) => Ok(d),
            _ => Err("有限診断の元構成がない".into()),
        },
        _ => Err("有限診断の元構成がない".into()),
    }
}
fn field(g: &Graph, r: NodeRef, name: &str) -> Result<NodeRef, ValidationFailure> {
    let d = local(g, r)?;
    let Json::Obj(w) = &d.part().wire else {
        return Err("有限診断のレコードがない".into());
    };
    d.part()
        .arguments
        .iter()
        .find(|a| Some(&a.wire()) == w.get(name))
        .copied()
        .ok_or_else(|| "有限診断の参照fieldがない".into())
}
fn elements(g: &Graph, r: NodeRef) -> Result<Vec<NodeRef>, ValidationFailure> {
    let d = local(g, r)?;
    let Json::Obj(w) = &d.part().wire else {
        return Err("有限Domainがない".into());
    };
    let Some(Json::Arr(items)) = w.get("elements") else {
        return Err("有限Domainの要素がない".into());
    };
    items
        .iter()
        .map(|item| {
            d.part()
                .arguments
                .iter()
                .find(|r| r.wire() == *item)
                .copied()
                .ok_or_else(|| "有限Domainの要素参照がない".into())
        })
        .collect()
}
fn pairs(g: &Graph, r: NodeRef) -> Result<Vec<(NodeRef, NodeRef)>, ValidationFailure> {
    let d = local(g, r)?;
    let Json::Obj(w) = &d.part().wire else {
        return Err("有限StateMapがない".into());
    };
    let Some(Json::Arr(items)) = w.get("pairs") else {
        return Err("有限StateMapの対応がない".into());
    };
    items
        .iter()
        .map(|item| {
            let Json::Arr(pair) = item else {
                return Err("対応が組でない".into());
            };
            if pair.len() != 2 {
                return Err("対応の長さが違う".into());
            }
            let refs = pair
                .iter()
                .map(|v| {
                    d.part()
                        .arguments
                        .iter()
                        .find(|r| r.wire() == *v)
                        .copied()
                        .ok_or_else(|| ValidationFailure::from("対応の参照がない"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok((refs[0], refs[1]))
        })
        .collect()
}
fn same_plan(a: &Request, b: &Request) -> bool {
    a.kind == b.kind
        && a.head == b.head
        && a.defaults == b.defaults
        && a.arguments
            .iter()
            .map(|x| (&x.name, &x.value))
            .collect::<BTreeMap<_, _>>()
            == b.arguments
                .iter()
                .map(|x| (&x.name, &x.value))
                .collect::<BTreeMap<_, _>>()
}
fn identity_pairs(
    g: &Graph,
    source: NodeRef,
    target: NodeRef,
    c: &mut Control,
) -> Result<Vec<(NodeRef, NodeRef)>, ValidationFailure> {
    let left = elements(g, source)?;
    if source == target {
        return Ok(left.into_iter().map(|r| (r, r)).collect());
    }
    let right = elements(g, target)?;
    let mut result = vec![];
    for a in &left {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let mut images = vec![];
        for z in &right {
            c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
            if g.scalar(*a)? == g.scalar(*z)? {
                images.push(*z);
            }
        }
        if images.len() != 1 || result.iter().any(|(_, z)| *z == images[0]) {
            return Err("同じ構成指定の有限状態の対応が一意でない".into());
        }
        result.push((*a, images[0]));
    }
    if left.len() != right.len() {
        return Err("同じ構成指定の有限状態の対応が全射でない".into());
    }
    Ok(result)
}
pub(super) fn compute(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    left: NodeRef,
    base: usize,
    witness: Arc<ArchitectureWitness>,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    let argument = |name| {
        request
            .arguments
            .iter()
            .find(|a| a.name == name)
            .ok_or_else(|| ValidationFailure::from("診断比較の引数がない"))
    };
    let right = reference(env, g, &argument("to")?.value)?;
    let along = reference(env, g, &argument("along")?.value)?;
    let left_system = field(g, left, "system")?;
    let right_system = field(g, right, "system")?;
    let data = local(g, left_system)?;
    let system = data.source.system.as_ref().ok_or("固定局所系がない")?;
    let operation = public_compose::op(g, along)?;
    operation.recheck(env.inputs, c).map_err(|e| match e {
        crate::construction::ConstructionFailure::Stopped(s) => ValidationFailure::Stop(s),
        e => ValidationFailure::Internal(format!("診断比較のOperation: {e:?}")),
    })?;
    let (from, to, _, _) = public_compose::components(g, along)?;
    let object = field(g, left_system, "base")?;
    let candidate = operation.map().candidate();
    // mapは対象外のUを根へ送る。局所系の観測位置・参照に対する実作用を確認する。
    let mut identity = true;
    for position in &system.fixed_positions {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let mut found = false;
        for (fact, image) in candidate.universe().iter().zip(candidate.images()) {
            c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
            if fact.snapshot == position.snapshot
                && fact.subject == position.subject
                && fact.field == position.field
            {
                found = true;
                identity &= fact == image;
            }
        }
        identity &= found;
    }
    let right_data = local(g, right_system)?;
    let right_plan = right_data
        .source
        .system
        .as_ref()
        .ok_or("比較先の局所系がない")?;
    let equation_side = integer::record(g, left)?.get("side") != Some(&Json::str("semantic"));
    let integer_side = system
        .integer
        .as_ref()
        .is_some_and(|d| !d.equation_only || equation_side);
    let right_integer_side = right_plan
        .integer
        .as_ref()
        .is_some_and(|d| !d.equation_only || equation_side);
    let rational_side = system.rational.as_ref().is_some_and(|d| !d.equation_only || equation_side);
    let right_rational_side = right_plan.rational.as_ref().is_some_and(|d| !d.equation_only || equation_side);
    let equivalent_finite = !rational_side
        && !right_rational_side
        && !integer_side
        && !right_integer_side
        && field(g, right_system, "base")? == object
        && same_plan(&data.source.request, &right_data.source.request);
    let supported = (left_system == right_system || equivalent_finite)
        && identity
        && operation.source() == operation.target()
        && operation.source().reading() == witness.construction().reading()
        && operation.source().root() == witness.construction().root()
        && (object == from || object == to);
    let transported = if !supported && integer_side {
        integer::between(env, g, left, right, along, c)?
    } else {
        None
    };
    let rational_transported = if !supported && rational_side {
        rational::between(env, g, left, right, along, c)?
    } else {
        None
    };
    let finite_transported = if !supported && !integer_side && !rational_side {
        finite_transport::between(env, g, left, right, along, c)?
    } else {
        None
    };
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let answer = if !supported
        && transported.is_none()
        && rational_transported.is_none()
        && finite_transported.is_none()
    {
        let (dependencies, scope) = if let Some(expression) = system.expression {
            let original = &data.source.parts[expression.0 - data.source.base];
            let expression = b.push(
                original.ty.clone(),
                original.construction,
                original.wire.clone(),
                original
                    .arguments
                    .iter()
                    .copied()
                    .chain([left, right, along])
                    .collect(),
                None,
                None,
            )?;
            (vec![expression], b.parts[0].scope.clone())
        } else {
            let mut scope = g.get(left)?.scope.clone();
            scope.merge(&g.get(right)?.scope);
            scope.merge(&g.get(along)?.scope);
            (vec![left, right, along], scope)
        };
        let reason = Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: QuestionKind::Compare,
                operand_types: vec![Type::Bool],
                method: "diagnostic_transport".into(),
            },
            request: request.id.clone(),
            dependencies,
            missing: vec![],
            location: None,
        };
        if let Some(part) = b.parts.first_mut() {
            part.reasons.push(reason.clone());
        }
        Answer {
            id: request.id.clone(),
            status: Decision::Undetermined,
            outputs: BTreeMap::new(),
            claim: None,
            evidence: vec![],
            reasons: vec![reason],
            scope,
        }
    } else if integer_side || rational_side {
        let result = if rational_side {
            rational::compare(
                &mut b,
                request,
                left,
                right,
                along,
                rational_transported.as_ref(),
                c,
            )
        } else {
            integer::compare(&mut b, request, left, right, along, transported.as_ref(), c)
        };
        match result {
            Ok(answer) => answer,
            Err(ValidationFailure::Stop(stop)) => {
                let mut scope = g.get(left)?.scope.clone();
                scope.merge(&g.get(right)?.scope);
                scope.merge(&g.get(along)?.scope);
                Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons: vec![Reason {
                        kind: ReasonKind::Stop(stop),
                        request: request.id.clone(),
                        dependencies: vec![left, right, along],
                        missing: vec![],
                        location: None,
                    }],
                    scope,
                }
            }
            Err(error) => return Err(error),
        }
    } else {
        let lm = field(g, left, "matching")?;
        let rm = field(g, right, "matching")?;
        let correspondence = if let Some(maps) = &finite_transported {
            maps.matching.clone()
        } else {
            identity_pairs(g, lm, rm, c)?
        };
        let lr = field(g, left, "restriction")?;
        let rr = field(g, right, "restriction")?;
        let global_domain = field(g, lr, "source")?;
        let target_domain = field(g, rr, "source")?;
        let global_pairs = if let Some(maps) = &finite_transported {
            maps.global.clone()
        } else {
            identity_pairs(g, global_domain, target_domain, c)?
        };
        let global_map = state_map(&mut b, global_domain, target_domain, &global_pairs)?;
        let matching_map = state_map(&mut b, lm, rm, &correspondence)?;
        let lp = pairs(g, lr)?;
        let rp = pairs(g, rr)?;
        for (x, y) in &lp {
            c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
            let mut transported = None;
            for (a, z) in &correspondence {
                c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
                if g.scalar(*a)? == g.scalar(*y)? {
                    transported = Some(*z);
                }
            }
            let transported = transported.ok_or("matchingの像がない")?;
            let mut global_image = None;
            for (a, z) in &global_pairs {
                c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
                if g.scalar(*a)? == g.scalar(*x)? {
                    global_image = Some(*z);
                }
            }
            let global_image = global_image.ok_or("大域状態の像がない")?;
            let mut commutes = false;
            for (a, z) in &rp {
                c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
                commutes |= g.scalar(*a)? == g.scalar(global_image)?
                    && g.scalar(*z)? == g.scalar(transported)?;
            }
            if !commutes {
                return Err("診断の制限写像が可換でない".into());
            }
        }
        let outside_image = finite_transported.as_ref().and_then(|m| m.outside_image);
        let status = if outside_image.is_none() {
            Decision::Established
        } else {
            Decision::Refuted
        };
        let mut conditions = if outside_image.is_none() {
            let global_inverse = if global_domain == target_domain && finite_transported.is_none() {
                global_map
            } else {
                state_map(
                    &mut b,
                    target_domain,
                    global_domain,
                    &global_pairs
                        .iter()
                        .map(|(a, z)| (*z, *a))
                        .collect::<Vec<_>>(),
                )?
            };
            let inverse = state_map(
                &mut b,
                rm,
                lm,
                &correspondence
                    .iter()
                    .map(|(a, z)| (*z, *a))
                    .collect::<Vec<_>>(),
            )?;
            vec![
                b.proposition(
                    "inverse_maps",
                    vec![global_map, global_inverse],
                    vec![along],
                    Decision::Established,
                )?,
                b.proposition(
                    "inverse_maps",
                    vec![matching_map, inverse],
                    vec![along],
                    Decision::Established,
                )?,
            ]
        } else {
            let count = change_result::value(
                &mut b,
                &Scalar::Z(
                    finite_transported
                        .as_ref()
                        .ok_or("有限輸送の像がない")?
                        .outside_count
                        .clone(),
                ),
            )?;
            let zero = change_result::value(&mut b, &Scalar::Z(num_bigint::BigInt::from(0)))?;
            vec![b.proposition(
                "equal",
                vec![count, zero],
                [global_map, matching_map]
                    .into_iter()
                    .chain(outside_image.iter().copied())
                    .collect(),
                status,
            )?]
        };
        conditions.push(b.proposition(
            "naturality",
            vec![global_map, matching_map, lr, rr],
            vec![along],
            Decision::Established,
        )?);
        let comparison = b.push(
            NodeType::Construction(T::Comparison),
            "comparison",
            Json::obj([
                ("kind", Json::str("diagnostics")),
                ("left", left.wire()),
                ("right", right.wire()),
                ("along", along.wire()),
                ("finite_map", global_map.wire()),
                ("conditions", refs(&conditions)),
            ]),
            [left, right, along, global_map]
                .into_iter()
                .chain(conditions)
                .collect(),
            None,
            None,
        )?;
        let proposition =
            b.proposition("diagnostics_preserved", vec![comparison], vec![], status)?;
        Answer {
            id: request.id.clone(),
            status,
            outputs: BTreeMap::from([
                ("comparison".into(), comparison),
                ("proposition".into(), proposition),
            ]),
            claim: Some(proposition),
            evidence: vec![],
            reasons: vec![],
            scope: b.parts[comparison.0 - base].scope.clone(),
        }
    };
    Ok(Source {
        base,
        parts: b.parts,
        scope_domains: vec![],
        answer,
        request: request.clone(),
        witness,
        system: None,
    })
}
