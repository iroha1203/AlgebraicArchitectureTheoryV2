//! 元viewの全体読取りを、同じDAGのOption値・通常Evaluationとして保持する。
use super::{
    construction_result as native, construction_result::ConstructionData as D,
    environment::Environment, object_component_diagram::ViewOrigin,
    object_reading_evaluation as body, result::*,
};
use crate::control::{Checkpoint, Control};
use crate::{construction::readings::InstanceApplication, issue::Location, types::Type};
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectEvaluation)?;
    Ok(())
}
// 通常のAST評価とは区別する。元式は封印されたObjectComponentsだけから得る。
pub(super) fn source(g: &Graph, n: &Node) -> Result<Option<NodeRef>, ValidationFailure> {
    let expression = match &n.payload {
        Some(Payload::Evaluation { expression, .. }) => Some(*expression),
        Some(Payload::Scalar(_)) if n.rule == Rule::Construction("evaluation") => {
            n.arguments.first().copied()
        }
        _ => None,
    };
    let Some(r) = expression else { return Ok(None) };
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Ok(None);
    };
    match &v.data {
        D::ObjectComponents(d) => Ok(d.view_origin(r)?.map(|_| r)),
        D::ViewFamily(d) => Ok(d.view_origin(r)?.map(|_| r)),
        _ => Ok(None),
    }
}
struct Plan {
    origin: ViewOrigin,
    support: Vec<Fact>,
    scope: Scope,
    reasons: Vec<Reason>,
    body: Option<NodeRef>,
    body_value: Option<NodeRef>,
    value: Option<Scalar>,
    applicability: &'static str,
    location: Location,
}
fn append(rs: &mut Vec<NodeRef>, r: NodeRef) {
    if !rs.contains(&r) {
        rs.push(r);
    }
}
impl Plan {
    fn arguments(&self) -> Vec<NodeRef> {
        let mut rs = vec![self.origin.expression, self.origin.architecture];
        for b in &self.origin.bindings {
            append(&mut rs, b.value);
        }
        if let Some(r) = self.body {
            append(&mut rs, r);
        }
        if let Some(r) = self.body_value {
            append(&mut rs, r);
        }
        rs
    }
    fn node(&self, payload: Payload, ty: NodeType, mut arguments: Vec<NodeRef>) -> Node {
        if let Payload::Evaluation { value: Some(r), .. } = &payload {
            append(&mut arguments, *r);
        }
        Node {
            ty,
            rule: Rule::Construction("evaluation"),
            arguments,
            support: self.support.clone(),
            scope: self.scope.clone(),
            reasons: self.reasons.clone(),
            evidence: vec![],
            judgment: None,
            payload: Some(payload),
        }
    }
    fn scalar_node(&self) -> Result<Node, ValidationFailure> {
        let value = self
            .value
            .clone()
            .ok_or("未確定view読取りにOption値を作れない")?;
        Ok(self.node(
            Payload::Scalar(value.clone()),
            NodeType::Value(value.ty()),
            self.arguments(),
        ))
    }
    fn evaluation_node(&self, value: Option<NodeRef>) -> Node {
        self.node(
            Payload::Evaluation {
                expression: self.origin.expression,
                bindings: self.origin.bindings.clone(),
                environment: Some(self.origin.architecture),
                parts: vec![Part {
                    location: self.location.clone(),
                    value: self.body_value,
                    residual: None,
                    children: self.body.into_iter().collect(),
                }],
                value,
                applicability: self.applicability,
            },
            NodeType::Evaluation(self.origin.returns.clone()),
            self.arguments(),
        )
    }
}
fn plan(
    g: &Graph,
    expression: NodeRef,
    evaluated: Option<NodeRef>,
) -> Result<Plan, ValidationFailure> {
    let (a, o) = body::origin(g, expression)?;
    if !o.parameters.is_empty() && !body::numeric_parameters(&o) {
        return Err("残るview parameterを閉じた読取りで評価できない".into());
    }
    let Type::Option(ty) = &o.returns else {
        return Err("元view全体の返り型がOptionでない".into());
    };
    let context = g.context_at(expression.0);
    if context != g.context_at(o.architecture.0)
        || context.frame.is_some()
        || context.instance.is_some()
        || context.iteration.is_some()
        || context.case.is_some()
    {
        return Err("元view全体の対象Contextが違う".into());
    }
    let location = Location::Law {
        span: native::Witness::Architecture(a.clone())
            .inputs()
            .law()
            .exprs()
            .get(o.body)
            .ok_or("元view bodyの出現がない")?
            .span,
    };
    let mut support = vec![];
    let mut scope = Scope::default();
    let mut reasons = vec![];
    for r in [o.expression, o.architecture]
        .into_iter()
        .chain(o.bindings.iter().map(|b| b.value))
    {
        g.tick()?;
        let n = g.get(r)?;
        support.extend(n.support.iter().cloned());
        scope.merge(&n.scope);
        reasons.extend(n.reasons.iter().cloned());
    }
    let mut body_value = None;
    let (value, applicability) = match &o.application {
        InstanceApplication::NotApplicable => {
            if evaluated.is_some() {
                return Err("非適用viewのbodyを全体読取りに加えた".into());
            }
            (
                Some(Scalar::Option {
                    element: (**ty).clone(),
                    value: None,
                }),
                "not_applicable",
            )
        }
        InstanceApplication::Applicable { conditions } if !conditions.is_empty() => {
            if evaluated.is_some() {
                return Err("所属未確定viewのbodyを全体読取りに加えた".into());
            }
            let mut missing = native::missing(
                native::Witness::Architecture(a.clone()).request(),
                conditions.iter().map(|c| c.slot().clone()).collect(),
            );
            for r in &mut missing {
                r.dependencies = vec![expression];
                r.location = Some(location.clone());
            }
            reasons.extend(missing);
            (None, "undetermined")
        }
        InstanceApplication::Applicable { .. } => {
            let r = evaluated.ok_or("適用済みviewの実body評価がない")?;
            let n = g.get(r)?;
            let ctx = g.context_at(r.0);
            let index = ctx.instance.ok_or("view bodyの元instanceがない")?;
            let i =
                body::instance_inputs(g, index, r.0)?.ok_or("view bodyが元view instanceでない")?;
            let record = g
                .instances
                .get(index)
                .ok_or("view bodyの実instanceがない")?;
            let Some(Payload::Evaluation {
                expression: e,
                bindings,
                environment,
                value,
                ..
            }) = &n.payload
            else {
                return Err("view bodyが通常Evaluationでない".into());
            };
            if i.origin != o
                || record.caller != context
                || ctx.request != context.request
                || ctx.frame.is_some()
                || ctx.iteration.is_some()
                || ctx.case.is_some()
                || n.ty != NodeType::Evaluation((**ty).clone())
                || *environment != Some(o.architecture)
                || bindings != &i.bindings
                || g.context_at(e.0) != ctx
                || e.0 >= r.0
            {
                return Err("view bodyの元対象/型/全束縛/Contextが違う".into());
            }
            let Some(Payload::Expression {
                location: actual, ..
            }) = &g.get(*e)?.payload
            else {
                return Err("view bodyの元Sourceがない".into());
            };
            if actual != &location {
                return Err("view bodyの原式出現が違う".into());
            }
            support.extend(n.support.iter().cloned());
            scope.merge(&n.scope);
            reasons.extend(n.reasons.iter().cloned());
            body_value = *value;
            let body_at = r.0;
            let wrapped = value
                .map(|r| -> Result<Scalar, ValidationFailure> {
                    if r.0 >= body_at {
                        return Err("view bodyの値が既出でない".into());
                    }
                    let value = g.scalar(r)?;
                    if value.ty() != **ty {
                        return Err("view bodyの実値型が違う".into());
                    }
                    Ok(Scalar::Option {
                        element: (**ty).clone(),
                        value: Some(Box::new(value.clone())),
                    })
                })
                .transpose()?;
            (wrapped, "applicable")
        }
    };
    support.sort();
    support.dedup();
    reasons.dedup();
    // 全引数の関数を、一つのOption値として公開しない。
    let value = if o.parameters.is_empty() { value } else { None };
    Ok(Plan {
        origin: o,
        support,
        scope,
        reasons,
        body: evaluated,
        body_value,
        value,
        applicability,
        location,
    })
}
fn actual_body(
    g: &Graph,
    n: &Node,
    expression: NodeRef,
) -> Result<Option<NodeRef>, ValidationFailure> {
    if let Some(Payload::Evaluation { parts, .. }) = &n.payload {
        let [p] = parts.as_slice() else {
            return Err("view全体評価に元body出現がない".into());
        };
        return match p.children.as_slice() {
            [] => Ok(None),
            [r] => Ok(Some(*r)),
            _ => Err("view全体評価の実bodyが一つでない".into()),
        };
    }
    let (_, o) = body::origin(g, expression)?;
    if matches!(&o.application, InstanceApplication::Applicable { conditions } if conditions.is_empty())
    {
        // 実bodyは型で選び、全辺の個数・順序は生成計画と後で完全照合する。
        let Type::Option(ty) = &o.returns else {
            return Err("view戻り型がOptionでない".into());
        };
        let mut matches = n.arguments.iter().copied().filter(
            |r| matches!(g.get(*r).map(|n|&n.ty),Ok(NodeType::Evaluation(t)) if t==ty.as_ref()),
        );
        let r = matches.next().ok_or("view値の元body評価がない")?;
        if matches.next().is_some() {
            return Err("view値の元body評価が重複する".into());
        }
        Ok(Some(r))
    } else {
        Ok(None)
    }
}
pub(super) fn dependencies(g: &Graph, n: &Node) -> Result<Vec<NodeRef>, ValidationFailure> {
    let expression = source(g, n)?.ok_or("全体評価の元viewがない")?;
    let mut rs = n.arguments.clone();
    append(&mut rs, expression);
    if let Some(Payload::Evaluation {
        bindings,
        environment,
        parts,
        value,
        ..
    }) = &n.payload
    {
        for b in bindings {
            append(&mut rs, b.value);
        }
        if let Some(r) = environment {
            append(&mut rs, *r);
        }
        if let Some(r) = value {
            append(&mut rs, *r);
        }
        for p in parts {
            for r in p.value.iter().chain(&p.residual).chain(&p.children) {
                append(&mut rs, *r);
            }
        }
    }
    Ok(rs)
}
pub(super) fn validate(g: &Graph, n: &Node, at: usize) -> Result<(), ValidationFailure> {
    let expression = source(g, n)?.ok_or("全体評価の元viewがない")?;
    if dependencies(g, n)?.iter().any(|r| r.0 >= at) {
        return Err("view全体評価の依存が既出でない".into());
    }
    let p = plan(g, expression, actual_body(g, n, expression)?)?;
    let expected = match &n.payload {
        Some(Payload::Scalar(_)) => p.scalar_node()?,
        Some(Payload::Evaluation { value, .. }) => {
            match (&p.value, value) {
                (Some(_), Some(r)) => {
                    if g.context_at(r.0) != g.context_at(expression.0) {
                        return Err("view Option値が別Context".into());
                    }
                    let expected = p.scalar_node()?;
                    let actual = g.get(*r)?;
                    if actual != &expected {
                        return Err("view全体評価のOption値が元bodyと違う".into());
                    }
                }
                (None, None) => (),
                _ => return Err("view全体評価の確定/欠測値が違う".into()),
            }
            p.evaluation_node(*value)
        }
        _ => return Err("view全体評価のpayloadが違う".into()),
    };
    if n != &expected {
        return Err("view全体評価の型/元式/辺/出現/metadataが違う".into());
    }
    Ok(())
}
#[derive(Debug)]
pub(super) enum Outcome {
    Parameters(Vec<(String, Type)>),
    Evaluation {
        evaluation: NodeRef,
        value: Option<NodeRef>,
    },
}
pub(super) fn evaluate(
    env: &Environment<'_>,
    g: &mut Graph,
    expression: NodeRef,
    c: &Control,
) -> Result<Outcome, ValidationFailure> {
    tick(c)?;
    if g.active != g.context_at(expression.0) {
        return Err("view全体生成が元Request Contextでない".into());
    }
    env.recheck_node(g, g.get(expression)?, expression.0)?;
    let (_, o) = body::origin(g, expression)?;
    if !o.parameters.is_empty() && !body::numeric_parameters(&o) {
        return Ok(Outcome::Parameters(o.parameters));
    }
    let evaluated = match body::evaluate(env, g, expression, c)? {
        body::Outcome::Body { side, .. } => Some(side.evaluation),
        body::Outcome::NotApplicable | body::Outcome::Conditional(_) => None,
        body::Outcome::Parameters(_) => return Err("閉じたviewに残るparameterがある".into()),
    };
    let p = plan(g, expression, evaluated)?;
    tick(c)?;
    let value = if p.value.is_some() {
        let node = p.scalar_node()?;
        env.validate(g, &node)?;
        Some(g.push(node)?)
    } else {
        None
    };
    tick(c)?;
    let node = p.evaluation_node(value);
    env.validate(g, &node)?;
    let evaluation = g.push(node)?;
    tick(c)?;
    Ok(Outcome::Evaluation { evaluation, value })
}
#[cfg(test)]
mod tests;
