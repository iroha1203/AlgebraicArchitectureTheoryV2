//! 同じ元Lawの完全束縛を、検査済み対象外テンプレートへ接続する。
use super::{
    construction_result::{ConstructionData as D, ConstructionValue, Witness},
    environment::Environment,
    law_evaluation as frames,
    result::*,
};
use archsig_common::canonical::Json;
use archsig_common::control::{Checkpoint, Control};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Data {
    pub base: NodeRef,
    pub template: NodeRef,
    pub architecture: NodeRef,
    pub wire: Json,
    pub arguments: Vec<NodeRef>,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
impl Data {
    pub fn scalar(&self) -> Option<&Scalar> {
        None
    }
    pub fn ty(&self) -> NodeType {
        NodeType::LawInstance
    }
    pub fn construction(&self) -> &'static str {
        "law_instance"
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        self.arguments.clone()
    }
    pub fn wire(&self) -> Json {
        self.wire.clone()
    }
    pub fn position(&self, limit: usize) -> Result<(), ValidationFailure> {
        if [self.base, self.template, self.architecture]
            .iter()
            .chain(&self.arguments)
            .any(|r| r.0 >= limit)
        {
            return Err("元Law特殊化の依存が既出Refでない".into());
        }
        Ok(())
    }
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectEvaluation)?;
    Ok(())
}
// 再帰的な特殊化を許さず、元三入力から構成したnative行を直接たどる。
fn leaf(graph: &Graph, r: NodeRef) -> Result<frames::Origin, ValidationFailure> {
    let Some(Payload::Construction(v)) = &graph.get(r)?.payload else {
        return Err("元Law特殊化の行がnativeでない".into());
    };
    if !matches!(v.data, D::FiniteLaw(_) | D::PolynomialLaw(_)) {
        return Err("元Law特殊化の行が元の有限/多項式行でない".into());
    }
    frames::origin(graph, r)?.ok_or_else(|| "元Law特殊化の元行がない".into())
}
fn expected(
    graph: &Graph,
    base: NodeRef,
    template: NodeRef,
    architecture: NodeRef,
) -> Result<(frames::Origin, Data), ValidationFailure> {
    let mut source = leaf(graph, base)?;
    let target = leaf(graph, template)?;
    if source.object != 0
        || !source.ready
        || source.outside
        || !target.outside
        || target.ready
        || !Arc::ptr_eq(&source.architecture, &target.architecture)
        || source.declaration != target.declaration
        || source.body != target.body
        || source.guard != target.guard
    {
        return Err("元Law特殊化のbase完全束縛・対象外テンプレートが違う".into());
    }
    frames::check_architecture(graph, architecture, &target)?;
    let context = graph.context_at(base.0);
    if graph.context_at(template.0) != context || graph.context_at(architecture.0) != context {
        return Err("元Law特殊化のRequest Contextが違う".into());
    }
    for fixed in &target.bindings {
        graph.tick()?;
        let bound = source
            .bindings
            .iter()
            .find(|b| b.name == fixed.name)
            .ok_or("元Law特殊化の固定parameterがない")?;
        if bound.ty != fixed.ty || graph.scalar(bound.value)? != graph.scalar(fixed.value)? {
            return Err("元Law特殊化の固定束縛の型・値が違う".into());
        }
    }
    let base_node = graph.get(base)?;
    let Some(Payload::Construction(v)) = &base_node.payload else {
        unreachable!()
    };
    let wire = v.wire();
    let mut arguments = vec![base, template, architecture];
    arguments.extend(&base_node.arguments);
    let mut support = base_node.support.clone();
    support.extend(graph.get(template)?.support.iter().cloned());
    support.extend(graph.get(architecture)?.support.iter().cloned());
    support.sort();
    support.dedup();
    // 全束縛済みの特殊化。テンプレートの未束縛parameterの全称Scopeは移さない。
    let mut scope = base_node.scope.clone();
    scope.merge(&graph.get(architecture)?.scope);
    source.object = target.object;
    source.ready = false;
    source.body_allowed = false;
    source.outside = true;
    let data = Data {
        base,
        template,
        architecture,
        wire,
        arguments,
        support,
        scope,
    };
    Ok((source, data))
}
pub(super) fn evaluation_origin(
    graph: &Graph,
    d: &Data,
) -> Result<Option<frames::Origin>, ValidationFailure> {
    Ok(Some(expected(graph, d.base, d.template, d.architecture)?.0))
}
pub(super) fn validate_node(
    graph: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let (row, expected) = expected(graph, d.base, d.template, d.architecture)?;
    let Witness::Architecture(w) = &v.witness else {
        return Err("元Law特殊化のArchitecture証拠がない".into());
    };
    if !Arc::ptr_eq(w, &row.architecture)
        || d != &expected
        || n.ty != d.ty()
        || n.rule != Rule::Construction(d.construction())
        || n.arguments != d.arguments
        || n.support != d.support
        || n.scope != d.scope
        || !n.evidence.is_empty()
        || !n.reasons.is_empty()
        || n.judgment.is_some()
    {
        return Err("元Law特殊化の原式・全束縛・型・由来・metadataが違う".into());
    }
    Ok(())
}
pub(super) fn instantiate(
    env: &Environment<'_>,
    graph: &mut Graph,
    base: NodeRef,
    template: NodeRef,
    architecture: NodeRef,
    c: &Control,
) -> Result<NodeRef, ValidationFailure> {
    <Data as super::result_kind::ResultKind>::compute_and_retain((
        env,
        graph,
        base,
        template,
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
        NodeRef,
        &'a Control,
    );
    type Output = NodeRef;
    fn compute_and_retain<'a, 'input: 'a>(
        input: Self::Input<'a, 'input>,
    ) -> Result<Self::Output, ValidationFailure> {
        let (env, graph, base, template, architecture, c) = input;
        tick(c)?;
        if graph.active != graph.context_at(base.0) {
            return Err("元Law特殊化の生成が元Request Contextでない".into());
        }
        env.recheck_law_evaluation_inputs(graph, base, architecture)?;
        env.recheck_law_evaluation_inputs(graph, template, architecture)?;
        let (row, d) = expected(graph, base, template, architecture)?;
        tick(c)?;
        let n = Node {
            ty: d.ty(),
            rule: Rule::Construction(d.construction()),
            arguments: d.arguments.clone(),
            support: d.support.clone(),
            scope: d.scope.clone(),
            evidence: vec![],
            reasons: vec![],
            judgment: None,
            payload: Some(Payload::Construction(Box::new(ConstructionValue {
                witness: Witness::Architecture(row.architecture),
                data: D::LawInstantiation(d),
            }))),
        };
        env.validate(graph, &n)?;
        let r = graph.push(n)?;
        tick(c)?;
        Ok(r)
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
        if let super::construction_result::ConstructionData::LawInstantiation(data) = &value.data {
            data.position(limit)?;
            graph.expect(data.base, &NodeType::LawInstance)?;
            graph.expect(data.template, &NodeType::LawInstance)?;
            graph.expect(
                data.architecture,
                &NodeType::Construction(super::construction_result::ConstructionType::Architecture),
            )?;
            env.recheck_law_evaluation_inputs(graph, data.base, data.architecture)?;
            env.recheck_law_evaluation_inputs(graph, data.template, data.architecture)?;
        }
        Ok(())
    }
}
#[cfg(test)]
mod tests;
