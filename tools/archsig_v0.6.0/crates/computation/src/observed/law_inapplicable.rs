//! 検査済み対象域の外にある元Lawを、未評価bodyと条件付き成立として保持する。
use super::{
    construction_result::{ArchitectureWitness, ConstructionData as D, ConstructionValue, Witness},
    environment::Environment,
    law_evaluation as frames,
    result::*,
};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::{canonical::Json, issue::Location, types::Type};
use std::{collections::BTreeMap, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Value(Scalar),
    Evaluation { value: NodeRef },
    Proposition { evaluation: NodeRef },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Data {
    pub origin: NodeRef,
    pub architecture: NodeRef,
    pub body: NodeRef,
    pub bindings: Vec<Binding>,
    pub location: Location,
    pub kind: Kind,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
impl Data {
    pub fn scalar(&self) -> Option<&Scalar> {
        match &self.kind {
            Kind::Value(v) => Some(v),
            _ => None,
        }
    }
    pub fn ty(&self) -> NodeType {
        match self.kind {
            Kind::Value(_) => NodeType::Value(Type::Bool),
            Kind::Evaluation { .. } => NodeType::Evaluation(Type::Bool),
            Kind::Proposition { .. } => NodeType::Proposition,
        }
    }
    pub fn construction(&self) -> &'static str {
        match self.kind {
            Kind::Value(_) | Kind::Evaluation { .. } => "evaluation",
            Kind::Proposition { .. } => "proposition",
        }
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        let mut a = vec![self.origin, self.architecture, self.body];
        a.extend(self.bindings.iter().map(|b| b.value));
        match self.kind {
            Kind::Value(_) => (),
            Kind::Evaluation { value } => a.push(value),
            Kind::Proposition { evaluation } => a.push(evaluation),
        }
        a
    }
    pub fn position(&self, limit: usize) -> Result<(), ValidationFailure> {
        if self.arguments().iter().any(|r| r.0 >= limit) {
            return Err(internal!("対象外Lawの由来・依存が既出Refでない").into());
        }
        Ok(())
    }
    pub fn wire(&self) -> Json {
        match &self.kind {
            Kind::Value(v) => v.wire(),
            Kind::Proposition { .. } => Json::obj([
                ("predicate", Json::str("law_holds")),
                ("operands", Json::Arr(vec![self.origin.wire()])),
                (
                    "quantifiers",
                    Json::Arr(
                        self.scope
                            .quantifiers
                            .iter()
                            .map(Quantifier::wire)
                            .collect(),
                    ),
                ),
            ]),
            Kind::Evaluation { value } => Json::obj([
                ("environment", self.architecture.wire()),
                ("expression", self.body.wire()),
                (
                    "bindings",
                    Json::Arr(
                        self.bindings
                            .iter()
                            .map(|b| {
                                Json::obj([("name", Json::str(&b.name)), ("value", b.value.wire())])
                            })
                            .collect(),
                    ),
                ),
                (
                    "parts",
                    Json::Arr(vec![Json::obj([
                        (
                            "location",
                            archsig_input::result::location_wire(&self.location),
                        ),
                        ("children", Json::Arr(vec![])),
                    ])]),
                ),
                ("value", value.wire()),
                ("applicability", Json::str("not_applicable")),
            ]),
        }
    }
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectEvaluation)?;
    Ok(())
}
fn original_body(graph: &Graph, origin: NodeRef) -> Result<NodeRef, ValidationFailure> {
    Ok(frames::origin(graph, origin)?
        .ok_or(internal!("対象外Lawの元行がない"))?
        .body_reference)
}
fn expected(
    graph: &Graph,
    d: &Data,
) -> Result<(frames::Origin, Vec<Fact>, Scope), ValidationFailure> {
    let row = frames::origin(graph, d.origin)?.ok_or(internal!("対象外Lawの検査済み元行がない"))?;
    frames::check_architecture(graph, d.architecture, &row)?;
    if !row.outside || row.ready {
        return Err(internal!("元Law行の対象外適用が確認されていない").into());
    }
    if graph.context_at(d.origin.0) != graph.context_at(d.architecture.0) {
        return Err(internal!("対象外Lawの元Request Contextが違う").into());
    }
    if d.body != original_body(graph, d.origin)? || d.bindings != row.bindings {
        return Err(internal!("対象外Lawの元body・全束縛が違う").into());
    }
    let body = graph.get(d.body)?;
    if body.ty != NodeType::Expression(Type::Bool) {
        return Err(internal!("対象外Lawのbody型がBoolでない").into());
    }
    let location = Location::Law {
        span: Witness::Architecture(row.architecture.clone())
            .inputs()
            .law()
            .exprs()
            .get(row.body)
            .ok_or(internal!("対象外Lawの元body式がない"))?
            .span,
    };
    if d.location != location {
        return Err(internal!("対象外Lawの元body出現が違う").into());
    }
    let mut support = graph.get(d.origin)?.support.clone();
    support.extend(graph.get(d.architecture)?.support.clone());
    support.sort();
    support.dedup();
    let mut scope = graph.get(d.origin)?.scope.clone();
    scope.merge(&graph.get(d.architecture)?.scope);
    Ok((row, support, scope))
}
pub(crate) fn validate_node(
    graph: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let (row, support, scope) = expected(graph, d)?;
    let Witness::Architecture(w) = &v.witness else {
        return Err(internal!("対象外Lawの元Architecture証拠がない").into());
    };
    if !Arc::ptr_eq(w, &row.architecture)
        || n.ty != d.ty()
        || n.rule != Rule::Construction(d.construction())
        || n.arguments != d.arguments()
        || d.support != support
        || n.support != support
        || d.scope != scope
        || n.scope != scope
        || !n.evidence.is_empty()
        || !n.reasons.is_empty()
    {
        return Err(internal!("対象外Lawの型・由来・支持・Scopeが違う").into());
    }
    let judgment = match d.kind {
        Kind::Proposition { .. } => Some(Judgment {
            status: Decision::Established,
            evidence: vec![],
            reasons: vec![],
        }),
        _ => None,
    };
    if n.judgment != judgment {
        return Err(internal!("対象外Lawの条件付き成立判断が違う").into());
    }
    let dependency = |r: NodeRef| -> Result<&Data, ValidationFailure> {
        let Some(Payload::Construction(child)) = &graph.get(r)?.payload else {
            return Err(internal!("対象外Lawの依存がnativeでない").into());
        };
        let D::OutsideLaw(child_data) = &child.data else {
            return Err(internal!("対象外Lawの依存が別の構成").into());
        };
        if child_data.origin != d.origin
            || child_data.architecture != d.architecture
            || child_data.body != d.body
            || child_data.bindings != d.bindings
            || child_data.location != d.location
            || child_data.support != support
            || child_data.scope != scope
        {
            return Err(internal!("対象外Lawの依存が別行・別対象である").into());
        }
        validate_node(graph, graph.get(r)?, child, child_data)?;
        Ok(child_data)
    };
    match &d.kind {
        Kind::Value(value) if *value == Scalar::Bool(true) => (),
        Kind::Evaluation { value }
            if matches!(dependency(*value)?.kind, Kind::Value(Scalar::Bool(true))) =>
        {
            ()
        }
        Kind::Proposition { evaluation }
            if matches!(dependency(*evaluation)?.kind, Kind::Evaluation { .. }) =>
        {
            ()
        }
        _ => return Err(internal!("対象外Lawの未評価body・値・評価依存が違う").into()),
    }
    Ok(())
}
fn put(
    env: &Environment<'_>,
    graph: &mut Graph,
    architecture: Arc<ArchitectureWitness>,
    data: Data,
) -> Result<NodeRef, ValidationFailure> {
    let n = Node {
        ty: data.ty(),
        rule: Rule::Construction(data.construction()),
        arguments: data.arguments(),
        support: data.support.clone(),
        scope: data.scope.clone(),
        evidence: vec![],
        reasons: vec![],
        judgment: matches!(data.kind, Kind::Proposition { .. }).then(|| Judgment {
            status: Decision::Established,
            evidence: vec![],
            reasons: vec![],
        }),
        payload: Some(Payload::Construction(Box::new(ConstructionValue {
            witness: Witness::Architecture(architecture),
            data: D::OutsideLaw(data),
        }))),
    };
    env.validate(graph, &n)?;
    graph.push(n)
}
pub(super) fn check(
    env: &Environment<'_>,
    graph: &mut Graph,
    origin: NodeRef,
    architecture: NodeRef,
    c: &Control,
) -> Result<Option<Answer>, ValidationFailure> {
    <Data as super::result_kind::ResultKind>::compute_and_retain((
        env,
        graph,
        origin,
        architecture,
        c,
    ))
}

impl super::result_kind::ResultKind for Data {
    type Stored = ();
    type Input<'a, 'input: 'a> = (
        &'a Environment<'input>,
        &'a mut Graph,
        NodeRef,
        NodeRef,
        &'a Control,
    );
    type Output = Option<Answer>;
    fn compute_and_retain<'a, 'input: 'a>(
        input: Self::Input<'a, 'input>,
    ) -> Result<Self::Output, ValidationFailure> {
        let (env, graph, origin, architecture, c) = input;
        tick(c)?;
        env.recheck_law_evaluation_inputs(graph, origin, architecture)?;
        let row = frames::origin(graph, origin)?.ok_or(internal!("対象外Lawの元行がない"))?;
        frames::check_architecture(graph, architecture, &row)?;
        if graph.active != graph.context_at(origin.0) {
            return Err(internal!("対象外Lawの元Request Contextが違う").into());
        }
        if !row.outside {
            return Ok(None);
        }
        let mut data = Data {
            origin,
            architecture,
            body: original_body(graph, origin)?,
            bindings: row.bindings.clone(),
            location: Location::Law {
                span: env
                    .indexes
                    .inputs
                    .law()
                    .exprs()
                    .get(row.body)
                    .ok_or(internal!("対象外Lawの元式がない"))?
                    .span,
            },
            kind: Kind::Value(Scalar::Bool(true)),
            support: vec![],
            scope: Scope::default(),
        };
        let (_, support, scope) = expected(graph, &data)?;
        data.support = support;
        data.scope = scope;
        tick(c)?;
        let value = put(env, graph, row.architecture.clone(), data.clone())?;
        tick(c)?;
        data.kind = Kind::Evaluation { value };
        let evaluation = put(env, graph, row.architecture.clone(), data.clone())?;
        tick(c)?;
        data.kind = Kind::Proposition { evaluation };
        let proposition = put(env, graph, row.architecture, data.clone())?;
        tick(c)?;
        Ok(Some(Answer {
            id: graph
                .requests
                .get(graph.active.request)
                .ok_or(internal!("対象外Lawの元Requestがない"))?
                .id
                .clone(),
            status: Decision::Established,
            outputs: BTreeMap::from([
                ("evaluation".into(), evaluation),
                ("proposition".into(), proposition),
            ]),
            claim: Some(proposition),
            evidence: vec![],
            reasons: vec![],
            scope: data.scope,
        }))
    }
    fn validate(
        &self,
        graph: &Graph,
        node: &Node,
        value: &super::construction_result::ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        validate_node(graph, node, value, self)
    }
    fn recheck(
        &self,
        env: &Environment<'_>,
        graph: &Graph,
        value: &super::construction_result::ConstructionValue,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        if let super::construction_result::ConstructionData::OutsideLaw(data) = &value.data {
            data.position(limit)?;
            graph.expect(data.origin, &NodeType::LawInstance)?;
            graph.expect(
                data.architecture,
                &NodeType::Construction(super::construction_result::ConstructionType::Architecture),
            )?;
            env.recheck_law_evaluation_inputs(graph, data.origin, data.architecture)?;
        }
        Ok(())
    }
}
#[cfg(test)]
mod tests;
