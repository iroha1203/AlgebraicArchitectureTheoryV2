//! 固定局所系の有限診断を、実際に恒等作用するOperationに沿って比較する。
use super::*;
use crate::observed::public_compose;
#[path = "local_integer_compare.rs"]
mod integer;
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
    let supported = system.finite.is_none()
        && left_system == right_system
        && identity
        && operation.source() == operation.target()
        && operation.source().reading() == witness.construction().reading()
        && operation.source().root() == witness.construction().root()
        && (object == from || object == to);
    let transported = if !supported && system.integer.is_some() {
        integer::between(env, g, left, right, along, c)?
    } else { None };
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let answer = if !supported && transported.is_none() {
        let original = &data.source.parts[system.expression.0 - data.source.base];
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
        let reason = Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: QuestionKind::Compare,
                operand_types: vec![Type::Bool],
                method: "diagnostic_transport".into(),
            },
            request: request.id.clone(),
            dependencies: vec![expression],
            missing: vec![],
            location: None,
        };
        b.parts[0].reasons.push(reason.clone());
        Answer {
            id: request.id.clone(),
            status: Decision::Undetermined,
            outputs: BTreeMap::new(),
            claim: None,
            evidence: vec![],
            reasons: vec![reason],
            scope: b.parts[0].scope.clone(),
        }
    } else if system.integer.is_some() {
        match integer::compare(&mut b, request, left, right, along, transported.as_ref(), c) {
            Ok(answer) => answer,
            Err(ValidationFailure::Stop(stop)) => {
                let mut scope = g.get(left)?.scope.clone();
                scope.merge(&g.get(right)?.scope);
                scope.merge(&g.get(along)?.scope);
                Answer {
                    id: request.id.clone(), status: Decision::Undetermined,
                    outputs: BTreeMap::new(), claim: None, evidence: vec![],
                    reasons: vec![Reason {kind: ReasonKind::Stop(stop),request:request.id.clone(),
                        dependencies:vec![left,right,along],missing:vec![],location:None}], scope,
                }
            }
            Err(error) => return Err(error),
        }
    } else {
        let lm = field(g, left, "matching")?;
        let rm = field(g, right, "matching")?;
        let le = elements(g, lm)?;
        let re = elements(g, rm)?;
        let mut correspondence = vec![];
        for a in &le {
            c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
            let mut matches = vec![];
            for z in &re {
                c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
                if g.scalar(*a)? == g.scalar(*z)? {
                    matches.push(*z);
                }
            }
            if matches.len() != 1 {
                return Err("固定局所系のmatching対応が一意でない".into());
            }
            correspondence.push((*a, matches[0]));
        }
        if le.len() != re.len() {
            return Err("固定局所系のmatching対応が全射でない".into());
        }
        let global = elements(g, system.domain)?;
        let global_map = state_map(
            &mut b,
            system.domain,
            system.domain,
            &global.iter().map(|r| (*r, *r)).collect::<Vec<_>>(),
        )?;
        let matching_map = state_map(&mut b, lm, rm, &correspondence)?;
        let inverse = state_map(
            &mut b,
            rm,
            lm,
            &correspondence
                .iter()
                .map(|(a, z)| (*z, *a))
                .collect::<Vec<_>>(),
        )?;
        let lr = field(g, left, "restriction")?;
        let rr = field(g, right, "restriction")?;
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
            let mut commutes = false;
            for (a, z) in &rp {
                c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
                commutes |=
                    g.scalar(*a)? == g.scalar(*x)? && g.scalar(*z)? == g.scalar(transported)?;
            }
            if !commutes {
                return Err("診断の制限写像が可換でない".into());
            }
        }
        let conditions = vec![
            b.proposition(
                "inverse_maps",
                vec![global_map, global_map],
                vec![along],
                Decision::Established,
            )?,
            b.proposition(
                "inverse_maps",
                vec![matching_map, inverse],
                vec![along],
                Decision::Established,
            )?,
            b.proposition(
                "naturality",
                vec![global_map, matching_map, lr, rr],
                vec![along],
                Decision::Established,
            )?,
        ];
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
        let proposition = b.proposition(
            "diagnostics_preserved",
            vec![comparison],
            vec![],
            Decision::Established,
        )?;
        Answer {
            id: request.id.clone(),
            status: Decision::Established,
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
