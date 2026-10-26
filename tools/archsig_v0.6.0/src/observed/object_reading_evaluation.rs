//! 元object_readingの閉じたviewを、通常Evaluatorのinstanceへ接続する。
use super::{
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionValue, Witness,
    },
    control::{Checkpoint, Control},
    environment::Environment,
    object_component_diagram::ViewOrigin,
    result::*,
};
use crate::{
    canonical::Json,
    construction::readings::{InstanceApplication, MembershipCondition},
    types::Type,
};
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectEvaluation)?;
    Ok(())
}
pub(super) fn origin(
    g: &Graph,
    r: NodeRef,
) -> Result<(Arc<ArchitectureWitness>, ViewOrigin), ValidationFailure> {
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("元view式がnativeでない".into());
    };
    if let D::ViewFamily(d) = &v.data {
        return d.view_origin(r)?.ok_or_else(|| "有限view行が元読取り式でない".into());
    }
    let D::ObjectComponents(d) = &v.data else {
        return Err("元view式が元対象表にない".into());
    };
    d.view_origin(r)?
        .ok_or_else(|| "元式がviewのobject_readingでない".into())
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Kind {
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
#[derive(Clone, Debug)]
struct Source {
    architecture: Arc<ArchitectureWitness>,
    origin: ViewOrigin,
    base: usize,
    support: Vec<Fact>,
    scope: Scope,
}
#[derive(Clone, Debug)]
pub(crate) struct Data {
    source: Arc<Source>,
    kind: Kind,
}
impl PartialEq for Data {
    fn eq(&self, b: &Self) -> bool {
        Arc::ptr_eq(&self.source, &b.source) && self.kind == b.kind
    }
}
impl Eq for Data {}
fn metadata(g: &Graph, o: &ViewOrigin) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
    let mut support = vec![];
    let mut scope = Scope::default();
    for r in [o.expression, o.architecture, o.component]
        .into_iter()
        .chain(o.bindings.iter().map(|b| b.value))
    {
        g.tick()?;
        let n = g.get(r)?;
        support.extend(n.support.iter().cloned());
        scope.merge(&n.scope);
    }
    support.sort();
    support.dedup();
    Ok((support, scope))
}
impl Data {
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        match &self.kind {
            Kind::Parameter { value, .. } | Kind::Member { value, .. } => Some(value),
            _ => None,
        }
    }
    pub(super) fn ty(&self) -> NodeType {
        match &self.kind {
            Kind::Parameter { value, .. } => NodeType::Value(value.ty()),
            Kind::Member { .. } => NodeType::Value(Type::Unit),
            Kind::Domain { .. } => NodeType::Domain,
        }
    }
    pub(super) fn construction(&self) -> &'static str {
        if matches!(self.kind, Kind::Domain { .. }) {
            "domain"
        } else {
            "binding"
        }
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        let o = &self.source.origin;
        let mut rs = vec![o.expression, o.architecture, o.component];
        rs.extend(o.bindings.iter().map(|b| b.value));
        match &self.kind {
            Kind::Member { bindings, .. } => rs.extend(bindings),
            Kind::Domain { member } => rs.push(*member),
            _ => (),
        };
        rs.sort_by_key(|r| r.0);
        rs.dedup();
        rs
    }
    pub(super) fn wire(&self) -> Json {
        match &self.kind {
            Kind::Parameter { value, .. } => value.wire(),
            Kind::Member { .. } => Scalar::Unit.wire(),
            Kind::Domain { member } => Json::obj([
                ("kind", Json::str("finite")),
                ("type", Type::Unit.wire()),
                ("elements", Json::Arr(vec![member.wire()])),
            ]),
        }
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.source.support.clone(), self.source.scope.clone())
    }
    pub(super) fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        let n = self.source.origin.bindings.len();
        let offset = match &self.kind {
            Kind::Parameter { position, .. } if *position < n => *position,
            Kind::Member { .. } => n,
            Kind::Domain { .. } => n.checked_add(1).ok_or("view frameの位置が域外")?,
            _ => return Err("view parameterの位置が域外".into()),
        };
        if self.source.base.checked_add(offset) != Some(at)
            || self.arguments().iter().any(|r| r.0 >= at)
        {
            return Err("view frameの元位置/既出参照が違う".into());
        };
        Ok(())
    }
    fn checked(&self, g: &Graph) -> Result<(), ValidationFailure> {
        let (a, o) = origin(g, self.source.origin.expression)?;
        if !Arc::ptr_eq(&a, &self.source.architecture)
            || o != self.source.origin
            || (!o.parameters.is_empty() && !numeric_parameters(&o))
            || !matches!(&o.application,InstanceApplication::Applicable{conditions} if conditions.is_empty())
            || g.context_at(o.expression.0) != g.context_at(o.architecture.0)
        {
            return Err("view frameの元対象/式/閉じた適用が違う".into());
        }
        let (support, scope) = metadata(g, &o)?;
        if support != self.source.support || scope != self.source.scope {
            return Err("view frameの支持/Scopeが違う".into());
        }
        match &self.kind {
            Kind::Parameter { position, value } => {
                let b = o.bindings.get(*position).ok_or("view parameterがない")?;
                if value != g.scalar(b.value)? || value.ty() != b.ty {
                    return Err("view parameterの元型/値が違う".into());
                }
            }
            Kind::Member { bindings, .. } => {
                if !matches!(
                    &self.kind,
                    Kind::Member {
                        value: Scalar::Unit,
                        ..
                    }
                ) || bindings.len() != o.bindings.len()
                {
                    return Err("view memberの全束縛がない".into());
                }
                for (i, r) in bindings.iter().enumerate() {
                    let d = frame(g, *r)?;
                    d.position(r.0)?;
                    if !Arc::ptr_eq(&d.source, &self.source)
                        || !matches!(&d.kind,Kind::Parameter{position,..} if *position==i)
                    {
                        return Err("view memberの束縛順/元由来が違う".into());
                    }
                    d.checked(g)?;
                }
            }
            Kind::Domain { member } => {
                let d = frame(g, *member)?;
                d.position(member.0)?;
                if !Arc::ptr_eq(&d.source, &self.source) || !matches!(d.kind, Kind::Member { .. }) {
                    return Err("viewの元memberが違う".into());
                };
                d.checked(g)?;
            }
        };
        Ok(())
    }
}
fn frame(g: &Graph, r: NodeRef) -> Result<&Data, ValidationFailure> {
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("view frameがnativeでない".into());
    };
    let D::ObjectReadingFrame(d) = &v.data else {
        return Err("view frameが別構成".into());
    };
    Ok(d)
}
pub(super) fn validate_node(
    g: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    d.checked(g)?;
    let Witness::Architecture(a) = &v.witness else {
        return Err("view frameのArchitectureがない".into());
    };
    if !Arc::ptr_eq(a, &d.source.architecture)
        || n.ty != d.ty()
        || n.rule != Rule::Construction(d.construction())
        || n.arguments != d.arguments()
        || n.support != d.source.support
        || n.scope != d.source.scope
        || !n.evidence.is_empty()
        || !n.reasons.is_empty()
        || n.judgment.is_some()
    {
        return Err("view frameの元由来/型/辺/metadataが違う".into());
    };
    Ok(())
}
pub(super) struct Inputs {
    pub origin: ViewOrigin,
    pub bindings: Vec<Binding>,
}
pub(super) fn instance_inputs(
    g: &Graph,
    index: usize,
    limit: usize,
) -> Result<Option<Inputs>, ValidationFailure> {
    let record = g.instances.get(index).ok_or("view instanceがない")?;
    let Some(Payload::Construction(v)) = &g.get(record.domain)?.payload else {
        return Ok(None);
    };
    let D::ObjectReadingFrame(d) = &v.data else {
        return Ok(None);
    };
    let Kind::Domain { member } = &d.kind else {
        return Err("view instanceの元Domainが違う".into());
    };
    let o = &d.source.origin;
    d.checked(g)?;
    d.position(record.domain.0)?;
    if record.source != o.expression
        || record.member != *member
        || record.caller != g.context_at(o.expression.0)
        || record.caller.frame.is_some()
        || record.caller.instance.is_some()
        || record.caller.iteration.is_some()
        || record.caller.case.is_some()
        || [record.source, record.domain, record.member, o.architecture]
            .iter()
            .any(|r| r.0 >= limit || g.context_at(r.0) != record.caller)
    {
        return Err("view instanceの元式/Context/既出参照が違う".into());
    }
    let m = frame(g, *member)?;
    let Kind::Member { bindings, .. } = &m.kind else {
        return Err("viewの実memberがない".into());
    };
    let mut actual = vec![];
    for (i, r) in bindings.iter().enumerate() {
        let d = frame(g, *r)?;
        d.position(r.0)?;
        if r.0 >= limit || g.context_at(r.0) != record.caller || !Arc::ptr_eq(&d.source, &m.source)
        {
            return Err("view実束縛のContext/由来が違う".into());
        }
        let b = o.bindings.get(i).ok_or("view実束縛が域外")?;
        actual.push(Binding {
            name: b.name.clone(),
            ty: b.ty.clone(),
            value: *r,
        });
    }
    Ok(Some(Inputs {
        origin: o.clone(),
        bindings: actual,
    }))
}
pub(super) fn declaration(g: &Graph, index: usize) -> Result<Option<String>, ValidationFailure> {
    Ok(instance_inputs(g, index, g.nodes.len())?.map(|i| i.origin.declaration))
}
pub(super) fn architecture(
    g: &Graph,
    index: usize,
    limit: usize,
) -> Result<Option<NodeRef>, ValidationFailure> {
    Ok(instance_inputs(g, index, limit)?.map(|i| i.origin.architecture))
}
#[derive(Debug)]
pub(super) enum Outcome {
    NotApplicable,
    Conditional(Vec<MembershipCondition>),
    Parameters(Vec<(String, Type)>),
    Body {
        instance: usize,
        side: super::evaluate::RelationSide,
    },
}
fn put(g: &mut Graph, source: Arc<Source>, kind: Kind) -> Result<NodeRef, ValidationFailure> {
    let d = Data { source, kind };
    d.position(g.nodes.len())?;
    d.checked(g)?;
    native::retain(
        g,
        ConstructionValue {
            witness: Witness::Architecture(d.source.architecture.clone()),
            data: D::ObjectReadingFrame(d),
        },
        vec![],
        vec![],
        None,
    )
}
pub(super) fn numeric_parameters(o: &ViewOrigin) -> bool {
    !o.parameters.is_empty() && o.parameters.iter().all(|(_, ty)| matches!(ty, Type::Z | Type::Q))
}
pub(super) fn evaluate(
    env: &Environment<'_>,
    g: &mut Graph,
    expression: NodeRef,
    c: &mut Control,
) -> Result<Outcome, ValidationFailure> {
    tick(c)?;
    if g.active != g.context_at(expression.0) {
        return Err("view body生成が元Request Contextでない".into());
    }
    env.recheck_node(g, g.get(expression)?, expression.0)?;
    let (a, o) = origin(g, expression)?;
    env.recheck_node(g, g.get(o.architecture)?, o.architecture.0)?;
    match &o.application {
        InstanceApplication::NotApplicable => return Ok(Outcome::NotApplicable),
        InstanceApplication::Applicable { conditions } if !conditions.is_empty() => {
            return Ok(Outcome::Conditional(conditions.clone()));
        }
        _ => (),
    };
    if !o.parameters.is_empty() && !numeric_parameters(&o) {
        return Ok(Outcome::Parameters(o.parameters.clone()));
    }
    let (support, scope) = metadata(g, &o)?;
    // このframeは固定済みの対象束縛だけを運ぶ。残る数値軸は式評価のTypeDomainで保持する。
    let source = Arc::new(Source {
        architecture: a,
        origin: o.clone(),
        base: g.nodes.len(),
        support,
        scope,
    });
    let mut bindings = vec![];
    for (position, b) in o.bindings.iter().enumerate() {
        tick(c)?;
        let value = g.scalar(b.value)?.clone();
        bindings.push(put(g, source.clone(), Kind::Parameter { position, value })?)
    }
    tick(c)?;
    let member = put(
        g,
        source.clone(),
        Kind::Member {
            bindings,
            value: Scalar::Unit,
        },
    )?;
    tick(c)?;
    let domain = put(g, source, Kind::Domain { member })?;
    let index = g.instances.len();
    g.instances.push(super::call::Instance {
        caller: g.active,
        source: expression,
        domain,
        member,
    });
    let request = g
        .requests
        .get(g.active.request)
        .ok_or("元view Requestがない")?
        .clone();
    let declaration = env
        .inputs
        .law()
        .declarations
        .get(&o.declaration)
        .ok_or("元view宣言がない")?;
    let side =
        super::evaluate::instance_expression(env, g, c, &request, declaration, index, o.body)?;
    let Type::Option(body_type) = &o.returns else {
        return Err("元view読取りの型がOptionでない".into());
    };
    if g.get(side.expression)?.ty != NodeType::Expression((**body_type).clone())
        || g.get(side.evaluation)?.ty != NodeType::Evaluation((**body_type).clone())
    {
        return Err("view bodyの元の戻り型が違う".into());
    }
    tick(c)?;
    Ok(Outcome::Body {
        instance: index,
        side,
    })
}
#[cfg(test)]
#[path = "object_reading_evaluation_tests.rs"]
mod tests;
