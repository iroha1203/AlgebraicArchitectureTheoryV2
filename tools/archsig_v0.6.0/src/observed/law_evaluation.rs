//! 元native Law行の完全束縛を、通常Evaluatorのinstance入力へ接続する。
use super::{
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionValue, Witness,
    },
    control::{Checkpoint, Control},
    environment::Environment,
    result::*,
};
use crate::{canonical::Json, types::Type};
use std::sync::Arc;

#[derive(Clone)]
pub(super) struct Origin {
    pub architecture: Arc<ArchitectureWitness>,
    pub object: usize,
    pub declaration: String,
    pub bindings: Vec<Binding>,
    pub body: usize,
    pub guard: Option<usize>,
    pub ready: bool,
    pub body_allowed: bool,
    pub scope: Scope,
}
pub(super) fn base_scope(
    a: &Arc<ArchitectureWitness>,
    name: &str,
) -> Result<Scope, ValidationFailure> {
    let witness = Witness::Architecture(a.clone());
    let mut scope = native::metadata(&ConstructionValue {
        witness: witness.clone(),
        data: D::ConstructionLabel(Scalar::Text("law_evaluation".into())),
    })?
    .1;
    let declaration = witness
        .inputs()
        .law()
        .declarations
        .get(name)
        .ok_or("元Law宣言がない")?;
    scope.readings.insert(declaration.reading.clone());
    Ok(scope)
}
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectEvaluation)?;
    Ok(())
}
pub(super) fn origin(graph: &Graph, r: NodeRef) -> Result<Option<Origin>, ValidationFailure> {
    let Some(Payload::Construction(v)) = &graph.get(r)?.payload else {
        return Ok(None);
    };
    match &v.data {
        D::FiniteLaw(d) => d.evaluation_origin(r),
        D::PolynomialLaw(d) => d.evaluation_origin(r),
        _ => Ok(None),
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Parameter {
        position: usize,
        value: Scalar,
    },
    Member {
        bindings: Vec<NodeRef>,
        value: Scalar,
    },
    Domain {
        member: NodeRef,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Data {
    pub origin: NodeRef,
    pub architecture: NodeRef,
    pub kind: Kind,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
impl Data {
    pub fn scalar(&self) -> Option<&Scalar> {
        match &self.kind {
            Kind::Parameter { value, .. } | Kind::Member { value, .. } => Some(value),
            _ => None,
        }
    }
    pub fn ty(&self) -> NodeType {
        match &self.kind {
            Kind::Domain { .. } => NodeType::Domain,
            Kind::Parameter { value, .. } | Kind::Member { value, .. } => {
                NodeType::Value(value.ty())
            }
        }
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        let mut refs = vec![self.origin, self.architecture];
        match &self.kind {
            Kind::Member { bindings, .. } => refs.extend(bindings),
            Kind::Domain { member } => refs.push(*member),
            _ => (),
        }
        refs
    }
    pub fn wire(&self) -> Json {
        match &self.kind {
            Kind::Domain { member } => Json::obj([
                ("kind", Json::str("finite")),
                ("type", Type::Unit.wire()),
                ("elements", Json::Arr(vec![member.wire()])),
            ]),
            Kind::Parameter { value, .. } | Kind::Member { value, .. } => value.wire(),
        }
    }
}
fn frame_value(
    graph: &Graph,
    r: NodeRef,
) -> Result<(&ConstructionValue, &Data), ValidationFailure> {
    let Some(Payload::Construction(v)) = &graph.get(r)?.payload else {
        return Err("元Law frameの値がnativeでない".into());
    };
    let D::LawFrame(d) = &v.data else {
        return Err("元Law frameの値が別の構成である".into());
    };
    Ok((v, d))
}
fn check_architecture(
    graph: &Graph,
    reference: NodeRef,
    row: &Origin,
) -> Result<(), ValidationFailure> {
    if row.object != 0
        && matches!(&graph.get(reference)?.payload,Some(Payload::Construction(v)) if matches!(v.data,D::Architecture {..}))
    {
        return Err("部分対象のLaw評価へbase Architectureを渡した".into());
    }
    let a = native::architecture_origin(graph, reference, row.object)?;
    if !Arc::ptr_eq(a, &row.architecture) {
        return Err("元Law frameのArchitectureが別の構成である".into());
    }
    Ok(())
}
fn checked_origin(graph: &Graph, d: &Data) -> Result<Origin, ValidationFailure> {
    let row = origin(graph, d.origin)?.ok_or("元Law frameが検査済み行でない")?;
    check_architecture(graph, d.architecture, &row)?;
    if !row.ready {
        return Err("元Law frameの対象・適用条件が違う".into());
    }
    Ok(row)
}
fn support(graph: &Graph, row: &Origin, kind: &Kind) -> Result<Vec<Fact>, ValidationFailure> {
    let selected: Vec<_> = match kind {
        Kind::Parameter { position, .. } => {
            vec![row.bindings.get(*position).ok_or("元parameter位置がない")?]
        }
        _ => row.bindings.iter().collect(),
    };
    let mut pending = vec![];
    for b in selected {
        graph.tick()?;
        pending.push(graph.scalar(b.value)?);
    }
    let mut facts = vec![];
    while let Some(value) = pending.pop() {
        graph.tick()?;
        match value {
            Scalar::Subject {
                snapshot, subject, ..
            } => facts.push(Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: None,
                atom: None,
            }),
            Scalar::Tuple(xs)
            | Scalar::List { items: xs, .. }
            | Scalar::Set { items: xs, .. }
            | Scalar::Data { args: xs, .. } => pending.extend(xs),
            Scalar::Map { pairs, .. } => {
                for (a, b) in pairs {
                    graph.tick()?;
                    pending.extend([a, b]);
                }
            }
            Scalar::Option { value: Some(v), .. } => pending.push(v),
            _ => (),
        }
    }
    facts.sort();
    facts.dedup();
    Ok(facts)
}
pub(super) fn validate_node(
    graph: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let row = checked_origin(graph, d)?;
    let Witness::Architecture(w) = &v.witness else {
        return Err("元Law frameの証人がない".into());
    };
    if !Arc::ptr_eq(w, &row.architecture)
        || n.ty != d.ty()
        || n.rule != Rule::Construction("domain")
        || n.arguments != d.arguments()
        || n.support != d.support
        || n.scope != d.scope
        || !n.reasons.is_empty()
        || !n.evidence.is_empty()
        || n.judgment.is_some()
        || d.scope != row.scope
    {
        return Err("元Law frameの型・由来・metadataが違う".into());
    }
    let original_support = support(graph, &row, &d.kind)?;
    if d.support != original_support {
        return Err("元Law frameの支持が違う".into());
    }
    match &d.kind {
        Kind::Parameter { position, value } => {
            let binding = row
                .bindings
                .get(*position)
                .ok_or("元Law parameter位置がない")?;
            if value.ty() != binding.ty || graph.scalar(binding.value)? != value {
                return Err("元Law parameterの型・値が違う".into());
            }
        }
        Kind::Member { bindings, value } => {
            if bindings.len() != row.bindings.len() || value != &Scalar::Unit {
                return Err("元Lawの完全束縛memberが違う".into());
            }
            for (position, r) in bindings.iter().enumerate() {
                let (_, p) = frame_value(graph, *r)?;
                if p.origin != d.origin
                    || p.architecture != d.architecture
                    || !matches!(p.kind,Kind::Parameter {position:i,..} if i==position)
                {
                    return Err("元Law memberのparameter由来が違う".into());
                }
            }
        }
        Kind::Domain { member } => {
            let (_, m) = frame_value(graph, *member)?;
            if m.origin != d.origin
                || m.architecture != d.architecture
                || !matches!(m.kind, Kind::Member { .. })
            {
                return Err("元Lawの束縛済み域のmemberが違う".into());
            }
        }
    }
    for r in d.arguments() {
        graph.get(r)?;
    }
    Ok(())
}
pub(super) struct Inputs {
    pub origin: Origin,
    pub architecture: NodeRef,
    pub bindings: Vec<Binding>,
}
pub(super) fn instance_inputs(
    graph: &Graph,
    index: usize,
    limit: usize,
) -> Result<Option<Inputs>, ValidationFailure> {
    let record = graph.instances.get(index).ok_or("元Law instanceがない")?;
    let Some(Payload::Construction(v)) = &graph.get(record.domain)?.payload else {
        return Ok(None);
    };
    let D::LawFrame(d) = &v.data else {
        return Ok(None);
    };
    let Kind::Domain { member } = &d.kind else {
        return Err("元Law instanceの域が違う".into());
    };
    if record.source != d.origin
        || record.member != *member
        || record.caller != graph.context_at(d.origin.0)
        || record.caller.frame.is_some()
        || record.caller.instance.is_some()
        || record.caller.iteration.is_some()
        || record.caller.case.is_some()
        || [record.source, record.domain, record.member, d.architecture]
            .iter()
            .any(|r| r.0 >= limit || graph.context_at(r.0) != record.caller)
    {
        return Err("元Law instanceの元行・member・既出Contextが違う".into());
    }
    let row = checked_origin(graph, d)?;
    let (_, m) = frame_value(graph, *member)?;
    if m.origin != d.origin || m.architecture != d.architecture {
        return Err("元Law memberが別対象である".into());
    }
    let Kind::Member { bindings, .. } = &m.kind else {
        return Err("元Lawの完全束縛がない".into());
    };
    if bindings.len() != row.bindings.len() {
        return Err("元Lawの全parameterが揃わない".into());
    }
    let mut result = vec![];
    for (position, (actual, expected)) in bindings.iter().zip(&row.bindings).enumerate() {
        if actual.0 >= limit || graph.context_at(actual.0) != record.caller {
            return Err("元Law parameterのContextが違う".into());
        }
        let (_, p) = frame_value(graph, *actual)?;
        if p.origin != d.origin
            || p.architecture != d.architecture
            || !matches!(p.kind,Kind::Parameter {position:i,..} if i==position)
            || graph.scalar(*actual)? != graph.scalar(expected.value)?
        {
            return Err("元Lawのparameter順・値・由来が違う".into());
        }
        result.push(Binding {
            name: expected.name.clone(),
            ty: expected.ty.clone(),
            value: *actual,
        });
    }
    Ok(Some(Inputs {
        origin: row,
        architecture: d.architecture,
        bindings: result,
    }))
}
pub(super) fn declaration(
    graph: &Graph,
    index: usize,
) -> Result<Option<String>, ValidationFailure> {
    Ok(instance_inputs(graph, index, graph.nodes.len())?.map(|i| i.origin.declaration))
}
pub(super) fn architecture(
    graph: &Graph,
    index: usize,
    limit: usize,
) -> Result<Option<NodeRef>, ValidationFailure> {
    Ok(instance_inputs(graph, index, limit)?.map(|i| i.architecture))
}
pub(super) fn body_guard(
    graph: &Graph,
    index: usize,
    span: (usize, usize),
    limit: usize,
) -> Result<(bool, Option<NodeRef>), ValidationFailure> {
    let Some(i) = instance_inputs(graph, index, limit)? else {
        return Ok((true, None));
    };
    let witness = Witness::Architecture(i.origin.architecture.clone());
    let law = witness.inputs().law();
    let body = law
        .exprs
        .get(i.origin.body)
        .ok_or("元Law body式がない")?
        .span;
    if !(body.0 <= span.0 && span.1 <= body.1) {
        return Ok((true, None));
    }
    let Some(guard) = i.origin.guard else {
        return Ok((true, None));
    };
    let expected = law.exprs.get(guard).ok_or("元Law guard式がない")?.span;
    let record = &graph.instances[index];
    let mut found = None;
    for (at, node) in graph.nodes.iter().enumerate().take(limit) {
        graph.tick()?;
        let context = graph.context_at(at);
        if context.instance != Some(index)
            || context.frame.is_some()
            || context.iteration.is_some()
            || context.case.is_some()
        {
            continue;
        }
        let Some(Payload::Evaluation {
            expression,
            environment,
            ..
        }) = &node.payload
        else {
            continue;
        };
        if *environment != Some(i.architecture) || context.request != record.caller.request {
            continue;
        }
        if matches!(&graph.get(*expression)?.payload,Some(Payload::Expression {location:crate::issue::Location::Law {span},..}) if *span==expected)
        {
            if found.replace(NodeRef(at)).is_some() {
                return Err("元Law guardの完成評価が重複".into());
            }
        }
    }
    Ok((
        i.origin.body_allowed,
        Some(found.ok_or("元Law bodyより先のguard評価がない")?),
    ))
}

fn put(
    graph: &mut Graph,
    row: &Origin,
    origin: NodeRef,
    architecture: NodeRef,
    kind: Kind,
) -> Result<NodeRef, ValidationFailure> {
    let support = support(graph, row, &kind)?;
    native::retain(
        graph,
        ConstructionValue {
            witness: Witness::Architecture(row.architecture.clone()),
            data: D::LawFrame(Data {
                origin,
                architecture,
                kind,
                support,
                scope: row.scope.clone(),
            }),
        },
        vec![],
        vec![],
        None,
    )
}
#[derive(Clone, Debug)]
pub(super) struct Evaluations {
    pub origin: NodeRef,
    pub guard: Option<NodeRef>,
    pub body: Option<NodeRef>,
    pub instance: Option<usize>,
}
pub(super) fn prepare_instance(
    env: &Environment<'_>,
    graph: &mut Graph,
    origin: NodeRef,
    architecture: NodeRef,
    c: &mut Control,
) -> Result<Option<(Origin, usize)>, ValidationFailure> {
    tick(c)?;
    env.recheck_law_evaluation_inputs(graph, origin, architecture)?;
    let Some(row) = self::origin(graph, origin)? else {
        return Err("評価する元native Law行がない".into());
    };
    check_architecture(graph, architecture, &row)?;
    let caller = graph.active;
    if caller != graph.context_at(origin.0) {
        return Err("Law評価の元Request Contextが違う".into());
    }
    if !row.ready {
        return Ok(None);
    }
    let mut bindings = vec![];
    for (position, b) in row.bindings.iter().enumerate() {
        tick(c)?;
        bindings.push(put(
            graph,
            &row,
            origin,
            architecture,
            Kind::Parameter {
                position,
                value: graph.scalar(b.value)?.clone(),
            },
        )?);
    }
    // 全parameterを固定済みの一点。元の全parameter域を有限化する域ではない。
    let member = put(
        graph,
        &row,
        origin,
        architecture,
        Kind::Member {
            bindings,
            value: Scalar::Unit,
        },
    )?;
    let domain = put(graph, &row, origin, architecture, Kind::Domain { member })?;
    let instance = graph.instances.len();
    graph.instances.push(super::call::Instance {
        caller,
        source: origin,
        domain,
        member,
    });
    Ok(Some((row, instance)))
}
pub(super) fn evaluate(
    env: &Environment<'_>,
    graph: &mut Graph,
    origin: NodeRef,
    architecture: NodeRef,
    c: &mut Control,
) -> Result<Evaluations, ValidationFailure> {
    let Some((row, instance)) = prepare_instance(env, graph, origin, architecture, c)? else {
        return Ok(Evaluations {
            origin,
            guard: None,
            body: None,
            instance: None,
        });
    };
    let caller = graph.instances[instance].caller;
    let request = graph
        .requests
        .get(caller.request)
        .ok_or("元Law評価Requestがない")?
        .clone();
    let declaration = env
        .inputs
        .law()
        .declarations
        .get(&row.declaration)
        .ok_or("元Law宣言がない")?;
    let guard = row
        .guard
        .map(|id| {
            super::evaluate::instance_expression(env, graph, c, &request, declaration, instance, id)
                .map(|e| e.evaluation)
        })
        .transpose()?;
    let guard_false = guard
        .map(|r| -> Result<bool, ValidationFailure> {
            let Some(Payload::Evaluation { value, .. }) = &graph.get(r)?.payload else {
                return Err("元guardが通常評価でない".into());
            };
            Ok(graph.boolean(*value)? == Some(false))
        })
        .transpose()?
        .unwrap_or(false);
    let body = if row.body_allowed && !guard_false {
        Some(
            super::evaluate::instance_expression(
                env,
                graph,
                c,
                &request,
                declaration,
                instance,
                row.body,
            )?
            .evaluation,
        )
    } else {
        None
    };
    Ok(Evaluations {
        origin,
        guard,
        body,
        instance: Some(instance),
    })
}

#[cfg(test)]
#[path = "law_evaluation_tests.rs"]
mod tests;
