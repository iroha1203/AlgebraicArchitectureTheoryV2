//! 元view instanceの全対象読取りを関数不変量とsignature軸へ接続する。
use super::{
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, Witness,
    },
    control::{Checkpoint, Control},
    environment::Environment,
    object_component_diagram::Diagram as Objects,
    object_reading_evaluation as reading, object_reading_result as whole,
    result::*,
    view_family,
};
use crate::{canonical::Json, types::Type};
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectViewFamily)?;
    Ok(())
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Value {
    object: NodeRef,
    expression: NodeRef,
    evaluation: NodeRef,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Output {
    declaration: String,
    parameters: Vec<(String, Type)>,
    bindings: Vec<Binding>,
    returns: Type,
    values: Vec<Value>,
    arguments: Vec<NodeRef>,
    support: Vec<Fact>,
    scope: Scope,
    reasons: Vec<Reason>,
}
#[derive(Clone, Debug)]
struct Source {
    architecture: Arc<ArchitectureWitness>,
    components: NodeRef,
    objects: Objects,
    instance: usize,
    evaluations: Vec<NodeRef>,
    base: usize,
    output: Output,
}
#[derive(Clone, Debug)]
pub(crate) struct Data {
    source: Arc<Source>,
    axis: bool,
    output: Output,
}
impl PartialEq for Data {
    fn eq(&self, b: &Self) -> bool {
        Arc::ptr_eq(&self.source, &b.source) && self.axis == b.axis && self.output == b.output
    }
}
impl Eq for Data {}
fn original(
    env: &Environment<'_>,
    g: &Graph,
    components: NodeRef,
    c: &mut Control,
) -> Result<(Arc<ArchitectureWitness>, Objects), ValidationFailure> {
    tick(c)?;
    let n = g.get(components)?;
    env.recheck_node(g, n, components.0)?;
    let Some(Payload::Construction(v)) = &n.payload else {
        return Err("関数不変量の元対象表がnativeでない".into());
    };
    let D::ObjectComponents(d) = &v.data else {
        return Err("関数不変量の元対象表が別構成".into());
    };
    let (a, reference, objects) = d.retained_components();
    if objects.base != components
        || objects.objects.len() != a.readings().objects().len()
        || objects.architectures.len() != objects.objects.len()
        || !Arc::ptr_eq(&a, native::architecture_origin(g, reference, 0)?)
    {
        return Err("関数不変量の元全対象/Architectureが違う".into());
    }
    Ok((a, objects))
}
fn expressions(
    g: &Graph,
    a: &Arc<ArchitectureWitness>,
    objects: &Objects,
    instance: usize,
    c: &mut Control,
) -> Result<Vec<NodeRef>, ValidationFailure> {
    let row = a
        .readings()
        .instances()
        .get(instance)
        .ok_or("関数不変量の元instanceがない")?;
    if row.declaration().kind != "view" {
        return Err("関数不変量の元instanceがviewでない".into());
    }
    let rs = objects
        .readings
        .iter()
        .filter(|r| r.instance == instance)
        .collect::<Vec<_>>();
    if rs.len() != objects.objects.len() || rs.is_empty() {
        return Err("関数不変量の全対象の元式がない".into());
    }
    let mut out = vec![];
    for (object, r) in rs.into_iter().enumerate() {
        tick(c)?;
        let (owner, origin) = reading::origin(g, r.expression)?;
        if r.object != object
            || !Arc::ptr_eq(&owner, a)
            || origin.instance_index != instance
            || origin.object_index != object
            || objects.objects.get(object) != Some(&origin.component)
            || objects.architectures.get(object) != Some(&origin.architecture)
        {
            return Err("関数不変量の元instance/対象順/式の由来が違う".into());
        }
        out.push(r.expression);
    }
    Ok(out)
}
fn compute(
    g: &Graph,
    a: &Arc<ArchitectureWitness>,
    objects: &Objects,
    components: NodeRef,
    instance: usize,
    evaluations: &[NodeRef],
    c: &mut Control,
) -> Result<Output, ValidationFailure> {
    let rs = expressions(g, a, objects, instance, c)?;
    if evaluations.len() != rs.len() {
        return Err("関数不変量の全対象の評価がない".into());
    }
    let (_, first) = reading::origin(g, rs[0])?;
    let mut values = vec![];
    let mut arguments = vec![components];
    let mut support = vec![];
    let mut scope = Scope::default();
    let mut reasons = vec![];
    for (object, (expression, evaluation)) in rs.iter().zip(evaluations).enumerate() {
        tick(c)?;
        let (_, origin) = reading::origin(g, *expression)?;
        let n = g.get(*evaluation)?;
        let Some(Payload::Evaluation {
            expression: e,
            bindings,
            environment,
            ..
        }) = &n.payload
        else {
            return Err("関数不変量の値が通常Evaluationでない".into());
        };
        if origin.declaration != first.declaration
            || origin.parameters != first.parameters
            || origin.bindings != first.bindings
            || origin.returns != first.returns
            || *e != *expression
            || bindings != &origin.bindings
            || *environment != Some(origin.architecture)
            || n.ty != NodeType::Evaluation(origin.returns.clone())
            || g.context_at(evaluation.0) != g.context_at(components.0)
        {
            return Err("関数不変量の元宣言/全署名/束縛/対象評価が違う".into());
        }
        if origin.parameters.is_empty() {
            whole::validate(g, n, evaluation.0)?;
        } else {
            view_family::validate_family(g, n, evaluation.0)?;
        }
        values.push(Value {
            object: objects.objects[object],
            expression: *expression,
            evaluation: *evaluation,
        });
        arguments.extend([objects.objects[object], *expression, *evaluation]);
    }
    arguments.extend(first.bindings.iter().map(|b| b.value));
    arguments.sort_by_key(|r| r.0);
    arguments.dedup();
    for r in &arguments {
        tick(c)?;
        let n = g.get(*r)?;
        support.extend(n.support.iter().cloned());
        scope.merge(&n.scope);
        reasons.extend(n.reasons.iter().cloned());
    }
    support.sort();
    support.dedup();
    reasons.sort_by_key(|r| r.wire().canonical());
    reasons.dedup();
    Ok(Output {
        declaration: first.declaration,
        parameters: first.parameters,
        bindings: first.bindings,
        returns: first.returns,
        values,
        arguments,
        support,
        scope,
        reasons,
    })
}
impl Data {
    pub(super) fn ty(&self) -> NodeType {
        NodeType::Construction(if self.axis {
            T::SignatureAxis
        } else {
            T::Invariant
        })
    }
    pub(super) fn construction(&self) -> &'static str {
        if self.axis {
            "signature_axis"
        } else {
            "invariant"
        }
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        let mut rs = self.output.arguments.clone();
        if self.axis {
            rs.push(NodeRef(self.source.base));
        }
        rs
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.output.support.clone(), self.output.scope.clone())
    }
    pub(super) fn wire(&self) -> Json {
        if self.axis {
            return Json::obj([
                ("invariant", NodeRef(self.source.base).wire()),
                ("value_type", self.output.returns.wire()),
                ("selected", Json::Bool(true)),
            ]);
        }
        Json::obj([
            ("kind", Json::str("function")),
            ("declaration", Json::str(&self.output.declaration)),
            (
                "parameters",
                Json::Arr(
                    self.output
                        .parameters
                        .iter()
                        .map(|(name, ty)| {
                            Json::obj([("name", Json::str(name)), ("type", ty.wire())])
                        })
                        .collect(),
                ),
            ),
            (
                "bindings",
                Json::Arr(
                    self.output
                        .bindings
                        .iter()
                        .map(|b| {
                            Json::obj([("name", Json::str(&b.name)), ("value", b.value.wire())])
                        })
                        .collect(),
                ),
            ),
            ("returns", self.output.returns.wire()),
            (
                "values",
                Json::Arr(
                    self.output
                        .values
                        .iter()
                        .map(|v| {
                            Json::obj([
                                ("object", v.object.wire()),
                                ("expression", v.expression.wire()),
                                ("evaluation", v.evaluation.wire()),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
    }
    pub(super) fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        if self.source.base.checked_add(usize::from(self.axis)) != Some(at)
            || self.arguments().iter().any(|r| r.0 >= at)
        {
            return Err("関数不変量/軸の元生成位置/既出Refが違う".into());
        }
        Ok(())
    }
    fn node(&self) -> Node {
        let (support, scope) = self.metadata();
        Node {
            ty: self.ty(),
            rule: Rule::Construction(self.construction()),
            arguments: self.arguments(),
            support,
            scope,
            reasons: self.output.reasons.clone(),
            evidence: vec![],
            judgment: None,
            payload: Some(Payload::Construction(Box::new(ConstructionValue {
                witness: Witness::Architecture(self.source.architecture.clone()),
                data: D::ViewInvariant(self.clone()),
            }))),
        }
    }
}
#[derive(Clone, Debug)]
pub(super) struct Axis {
    pub instance: usize,
    pub invariant: NodeRef,
    pub signature: NodeRef,
}
#[derive(Debug)]
pub(super) struct Pending {
    pub instance: usize,
    pub expressions: Vec<NodeRef>,
    pub parameters: Vec<view_family::Parameter>,
}
#[derive(Debug)]
pub(super) struct Diagram {
    pub axes: Vec<Axis>,
    pub pending: Vec<Pending>,
}
pub(super) fn retain(
    env: &Environment<'_>,
    g: &mut Graph,
    components: NodeRef,
    c: &mut Control,
) -> Result<Diagram, ValidationFailure> {
    tick(c)?;
    if g.active != g.context_at(components.0) {
        return Err("関数不変量の生成が元Request Contextでない".into());
    }
    let (a, objects) = original(env, g, components, c)?;
    let mut diagram = Diagram {
        axes: vec![],
        pending: vec![],
    };
    for (instance, row) in a.readings().instances().iter().enumerate() {
        tick(c)?;
        if row.declaration().kind != "view" {
            continue;
        }
        let rs = expressions(g, &a, &objects, instance, c)?;
        let (_, o) = reading::origin(g, rs[0])?;
        // 全対象の元式は同じparameter域を共有する。保留なら評価の生成前に返す。
        if !o.parameters.is_empty() {
            let parameters = view_family::parameter_readings(env, g, rs[0], c)?;
            if parameters
                .iter()
                .any(|p| p.values.is_none() || !p.missing.is_empty())
            {
                diagram.pending.push(Pending {
                    instance,
                    expressions: rs,
                    parameters,
                });
                continue;
            }
        }
        let mut evaluations = vec![];
        for expression in rs {
            tick(c)?;
            let evaluation = if o.parameters.is_empty() {
                let whole::Outcome::Evaluation { evaluation, .. } =
                    whole::evaluate(env, g, expression, c)?
                else {
                    return Err("閉じた関数不変量に残parameterがある".into());
                };
                evaluation
            } else {
                let view_family::Outcome::Family(f) = view_family::evaluate(env, g, expression, c)?
                else {
                    return Err("有限関数不変量の全域が生成途中で変わった".into());
                };
                f.evaluation
            };
            evaluations.push(evaluation);
        }
        let output = compute(g, &a, &objects, components, instance, &evaluations, c)?;
        let source = Arc::new(Source {
            architecture: a.clone(),
            components,
            objects: objects.clone(),
            instance,
            evaluations,
            base: g.nodes.len(),
            output: output.clone(),
        });
        let invariant = NodeRef(source.base);
        for axis in [false, true] {
            tick(c)?;
            let data = Data {
                source: source.clone(),
                axis,
                output: output.clone(),
            };
            data.position(g.nodes.len())?;
            let node = data.node();
            env.validate(g, &node)?;
            g.push(node)?;
        }
        diagram.axes.push(Axis {
            instance,
            invariant,
            signature: NodeRef(source.base + 1),
        });
    }
    tick(c)?;
    Ok(diagram)
}
pub(super) fn validate_node(
    g: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let Witness::Architecture(a) = &v.witness else {
        return Err("関数不変量のconsumerが別種".into());
    };
    if !Arc::ptr_eq(a, &d.source.architecture)
        || d.output != d.source.output
        || n != &d.node()
        || &d.node() != n
    {
        return Err("関数不変量/軸の元由来/全対象/metadataが違う".into());
    }
    if d.axis {
        let Some(Payload::Construction(v)) = &g.get(NodeRef(d.source.base))?.payload else {
            return Err("signatureの関数Invariantがない".into());
        };
        let D::ViewInvariant(other) = &v.data else {
            return Err("signatureの参照が関数Invariantでない".into());
        };
        if other.axis || !Arc::ptr_eq(&other.source, &d.source) || other.output != d.output {
            return Err("signatureが別の関数Invariantを参照する".into());
        }
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_view_invariant(
        &self,
        g: &Graph,
        v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        let D::ViewInvariant(d) = &v.data else {
            return Ok(());
        };
        d.position(at)?;
        let mut c = self.control.clone();
        let (a, objects) = original(self, g, d.source.components, &mut c)?;
        if !Arc::ptr_eq(&a, &d.source.architecture) || objects != d.source.objects {
            return Err("関数不変量の元入力/全対象が違う".into());
        }
        for r in d.arguments() {
            tick(&mut c)?;
            self.recheck_node(g, g.get(r)?, r.0)?;
        }
        if compute(
            g,
            &a,
            &objects,
            d.source.components,
            d.source.instance,
            &d.source.evaluations,
            &mut c,
        )? != d.output
        {
            return Err("関数不変量の元instance/全域評価/支持が違う".into());
        }
        Ok(())
    }
}
#[cfg(test)]
#[path = "view_invariant_tests.rs"]
mod tests;
