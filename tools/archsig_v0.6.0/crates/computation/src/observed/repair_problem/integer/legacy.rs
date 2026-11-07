//! 既存の整数全解と元Assignmentへの接続。
use super::*;
/// 既存solve/repairの完成した整数結果も同じ元Assignment経路へ接続する。
pub(super) fn legacy(
    env: &Environment<'_>,
    g: &Graph,
    set: NodeRef,
    c: &Control,
) -> Result<Option<Arc<Shared>>, ValidationFailure> {
    let (base, witness) = change_result::candidate_origin(env, g, set)?;
    let origin = Witness::Architecture(witness.clone());
    let request = origin.request();
    if !is_prepare(env, request) {
        return Ok(None);
    };
    let field = |at: NodeRef, name: &str| -> Result<NodeRef, ValidationFailure> {
        let Some(Payload::Construction(value)) = &g.get(at)?.payload else {
            return Err(internal!("整数元結果の型付きrecordがない").into());
        };
        let wire = value.wire();
        let requested = fields(&wire)
            .and_then(|f| f.get(name))
            .ok_or(internal!("整数元結果の欄がない"))?;
        value
            .arguments()
            .into_iter()
            .find(|r| r.wire() == *requested)
            .ok_or_else(|| internal!("整数元結果の型付き辺がない").into())
    };
    let domain = if g.get(set)?.ty == NodeType::Construction(T::CandidateSpace) {
        set
    } else {
        field(set, "domain")?
    };
    for node in &g.nodes {
        tick(c)?;
        let Some(Payload::Construction(value)) = &node.payload else {
            continue;
        };
        let D::SharedRepair(d) = &value.data else {
            continue;
        };
        if d.index != 0 {
            continue;
        }
        let Some(state) = d.source.integer() else {
            continue;
        };
        if state.shared.problem.is_none() && state.shared.domain == domain {
            return Ok(Some(state.shared.clone()));
        }
    }
    use crate::observed::environment::repair_problem::integer::{self as compiler, Preparation};
    let linear = change_result::candidate_linear(env, g, set)?
        .ok_or(internal!("既存整数全解の表示を生成したfiberがない"))?;
    let compiled = env.with_request_context(g, request, || {
        let _selected = env.enter_architecture(g)?;
        compiler::from_linear(env, g, &witness, request, c, linear)
    })?;
    let Preparation::Ready(compiled) = compiled else {
        return Err(ValidationFailure::UnsupportedExpression {
            location: archsig_common::issue::Location::Law { span: (0, 0) },
            feature: "整数全解の復元に必要な現在の元式が未確定".into(),
        });
    };
    let Some(Payload::Construction(value)) = &g.get(domain)?.payload else {
        unreachable!()
    };
    let wire = value.wire();
    let Some(Json::Arr(instances)) = fields(&wire).and_then(|f| f.get("instances")) else {
        return Err(internal!("整数元候補域のinstanceがない").into());
    };
    let mut subjects = vec![];
    for subject in &compiled.subjects {
        let mut found = None;
        for instance in instances {
            tick(c)?;
            if let Some(wire) = fields(instance).and_then(|f| f.get("subject")) {
                for at in value.arguments() {
                    tick(c)?;
                    if at.wire() == *wire && g.scalar(at).ok() == Some(subject) {
                        found = Some(at);
                        break;
                    }
                }
            }
        }
        subjects.push(found.ok_or(internal!("整数元候補域のsubjectがない"))?);
    }
    let Some(Json::Arr(required)) = fields(&wire).and_then(|f| f.get("requirements")) else {
        return Err(internal!("整数元候補域のLawがない").into());
    };
    let mut requirements = vec![];
    for wire in required {
        let mut found = None;
        for at in value.arguments() {
            tick(c)?;
            if at.wire() == *wire {
                found = Some(at);
                break;
            }
        }
        requirements.push(found.ok_or(internal!("整数元候補域のLawの辺がない"))?);
    }
    let parameters = field(domain, "parameters")?;
    let parameter_module = field(parameters, "module")?;
    let ring = field(parameter_module, "ring")?;
    let action = field(domain, "action")?;
    let root = witness.construction().root();
    let root_type = env
        .indexes
        .subject(&root.snapshot, &root.subject)?
        .ty
        .to_string();
    let n = subjects.len();
    Ok(Some(Arc::new(Shared {
        compiled,
        input_domain: None,
        projection: None,
        witness,
        base,
        domain,
        problem: None,
        subjects,
        requirements,
        internal: vec![false; n],
        unit_rows: vec![vec![]; n],
        ring,
        parameter_module,
        action,
        root_type,
    })))
}
