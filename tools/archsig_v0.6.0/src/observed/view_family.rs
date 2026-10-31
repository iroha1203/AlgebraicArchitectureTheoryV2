//! 元viewの有限parameter全域・直積・具体rowを同じnative DAGへ保持する。
use super::{
    construction_result as native,
    construction_result::{ArchitectureWitness, ConstructionData as D, ConstructionValue, Witness},
    environment::{Environment, numeric_parameters},
    object_component_diagram::ViewOrigin,
    object_reading_evaluation as reading, object_reading_result as whole,
    result::*,
};
use crate::control::{Checkpoint, Control};
use crate::{
    canonical::Json,
    issue::Location,
    law::model::{Param, Signature},
    types::Type,
};
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectViewFamily)?;
    Ok(())
}
fn refs(rs: &[NodeRef]) -> Json {
    Json::Arr(rs.iter().map(|r| r.wire()).collect())
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Parameter {
    pub declaration: Param,
    pub values: Option<Vec<Scalar>>,
    pub missing: Vec<Fact>,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
fn symbolic(p: &Parameter) -> bool {
    p.values.is_none() && numeric_parameters::numeric_width(&p.declaration.ty).is_some()
}
pub(super) fn pending_parameters(ps: &[Parameter]) -> bool {
    ps.iter().any(|p| (!symbolic(p) && p.values.is_none()) || !p.missing.is_empty())
}
fn parameters(
    env: &Environment<'_>,
    g: &Graph,
    expression: NodeRef,
    c: &mut Control,
) -> Result<(Arc<ArchitectureWitness>, ViewOrigin, Vec<Parameter>), ValidationFailure> {
    let (a, o) = reading::origin(g, expression)?;
    if o.parameters.is_empty() {
        return Err("有限view族には残るparameterが必要".into());
    }
    let row = a
        .readings()
        .instances()
        .get(o.instance_index)
        .ok_or("元view instanceの位置がない")?;
    if row.declaration().name != o.declaration
        || row.applications().get(o.object_index) != Some(&o.application)
    {
        return Err("元view族の対象/宣言が違う".into());
    }
    let mut out = vec![];
    for (name, ty) in &o.parameters {
        tick(c)?;
        let mut ps = row.parameters().iter().filter(|p| p.name == *name);
        let p = ps.next().ok_or("元viewのparameter署名がない")?;
        if ps.next().is_some() || p.ty.erase() != *ty {
            return Err("元viewのparameter位置/型が違う".into());
        }
        let d = env.object_parameter_domain(p, row)?;
        let values = d
            .values
            .map(|values| {
                values
                    .iter()
                    .map(|v| super::finite_law_diagram::canonical_value(v, c))
                    .collect::<Result<Vec<_>, _>>()
            })
            .transpose()?;
        out.push(Parameter {
            declaration: p.clone(),
            values,
            missing: d.missing,
            support: d.support,
            scope: d.scope,
        });
    }
    if out.len() != row.parameters().len() {
        return Err("元viewの残parameter全体がない".into());
    }
    Ok((a, o, out))
}
pub(super) fn parameter_readings(
    env: &Environment<'_>,
    g: &Graph,
    expression: NodeRef,
    c: &mut Control,
) -> Result<Vec<Parameter>, ValidationFailure> {
    Ok(parameters(env, g, expression, c)?.2)
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Part {
    Value {
        scalar: Scalar,
        children: Vec<NodeRef>,
        wire: Json,
    },
    Domain {
        ty: Type,
        values: Vec<NodeRef>,
    },
    Row {
        origin: ViewOrigin,
        member: NodeRef,
    },
}
impl Part {
    fn ty(&self) -> NodeType {
        match self {
            Self::Value { scalar, .. } => NodeType::Value(scalar.ty()),
            Self::Domain { .. } => NodeType::Domain,
            Self::Row { origin, .. } => NodeType::Expression(origin.returns.clone()),
        }
    }
    fn construction(&self) -> &'static str {
        match self {
            Self::Value { .. } => "binding",
            Self::Domain { .. } => "domain",
            Self::Row { .. } => "expression",
        }
    }
    fn refs(&self) -> Vec<NodeRef> {
        match self {
            Self::Value { children, .. } => children.clone(),
            Self::Domain { values, .. } => values.clone(),
            Self::Row { origin, member } => std::iter::once(*member)
                .chain(origin.bindings.iter().map(|b| b.value))
                .collect(),
        }
    }
    fn wire(&self) -> Json {
        match self {
            Self::Value { wire, .. } => wire.clone(),
            Self::Domain { ty, values } => Json::obj([
                ("kind", Json::str("finite")),
                ("type", ty.wire()),
                ("elements", refs(values)),
            ]),
            Self::Row { origin: o, .. } => Json::obj([
                ("kind", Json::str("object_reading")),
                ("object", o.component.wire()),
                ("declaration", Json::str(&o.declaration)),
                ("parameters", Json::Arr(o.parameters.iter().map(|(name, ty)|
                    Json::obj([("name", Json::str(name)), ("type", ty.wire())])).collect())),
                (
                    "bindings",
                    Json::Arr(
                        o.bindings
                            .iter()
                            .map(|b| {
                                Json::obj([("name", Json::str(&b.name)), ("value", b.value.wire())])
                            })
                            .collect(),
                    ),
                ),
                ("returns", o.returns.wire()),
            ]),
        }
    }
}
#[derive(Clone, Debug)]
struct Source {
    architecture: Arc<ArchitectureWitness>,
    origin: ViewOrigin,
    parameters: Vec<Parameter>,
    base: usize,
    parts: Vec<Part>,
    domains: Vec<NodeRef>,
    product: NodeRef,
    rows: Vec<NodeRef>,
    support: Vec<Fact>,
    scope: Scope,
}
#[derive(Clone, Debug)]
pub(crate) struct Data {
    source: Arc<Source>,
    index: usize,
}
impl PartialEq for Data {
    fn eq(&self, b: &Self) -> bool {
        Arc::ptr_eq(&self.source, &b.source) && self.index == b.index
    }
}
impl Eq for Data {}
impl Data {
    fn part(&self) -> Result<&Part, ValidationFailure> {
        self.source
            .parts
            .get(self.index)
            .ok_or_else(|| "有限viewの構成位置が域外".into())
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        match self.source.parts.get(self.index) {
            Some(Part::Value { scalar, .. }) => Some(scalar),
            _ => None,
        }
    }
    pub(super) fn ty(&self) -> NodeType {
        self.source.parts[self.index].ty()
    }
    pub(super) fn scope_domain_type(&self) -> Option<&Type> {
        match self.source.parts.get(self.index) {
            Some(Part::Domain { ty, .. }) => Some(ty),
            _ => None,
        }
    }
    pub(super) fn construction(&self) -> &'static str {
        self.source.parts[self.index].construction()
    }
    pub(super) fn wire(&self) -> Json {
        self.source.parts[self.index].wire()
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        let mut rs = vec![
            self.source.origin.expression,
            self.source.origin.architecture,
        ];
        rs.extend(self.source.origin.bindings.iter().map(|b| b.value));
        rs.extend(self.source.parts[self.index].refs());
        if matches!(self.source.parts[self.index], Part::Row { .. }) {
            rs.extend(&self.source.domains);
            rs.push(self.source.product);
        }
        rs.sort_by_key(|r| r.0);
        rs.dedup();
        rs
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.source.support.clone(), self.source.scope.clone())
    }
    pub(super) fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        self.part()?;
        if self.source.base.checked_add(self.index) != Some(at)
            || self.arguments().iter().any(|r| r.0 >= at)
        {
            return Err("有限view構成の元位置/既出辺が違う".into());
        }
        Ok(())
    }
    pub(super) fn view_origin(
        &self,
        r: NodeRef,
    ) -> Result<Option<(Arc<ArchitectureWitness>, ViewOrigin)>, ValidationFailure> {
        self.position(r.0)?;
        match self.part()? {
            Part::Row { origin, .. } => {
                if origin.expression != r {
                    return Err("具体view行の元式位置が違う".into());
                }
                Ok(Some((self.source.architecture.clone(), origin.clone())))
            }
            _ => Ok(None),
        }
    }
    pub(super) fn recheck(
        &self,
        env: &Environment<'_>,
        g: &Graph,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        let (a, o, ps) = parameters(env, g, self.source.origin.expression, c)?;
        if !Arc::ptr_eq(&a, &self.source.architecture)
            || o != self.source.origin
            || ps != self.source.parameters
        {
            return Err("有限viewの元入力/対象/署名/全域が違う".into());
        }
        let expected = build_source(g, a, o, ps, self.source.base, c)?;
        if expected.parts != self.source.parts
            || expected.domains != self.source.domains
            || expected.product != self.source.product
            || expected.rows != self.source.rows
            || expected.support != self.source.support
            || expected.scope != self.source.scope
        {
            return Err("有限viewの全構成/順序/支持/Scopeが違う".into());
        }
        Ok(())
    }
}
fn push(
    parts: &mut Vec<Part>,
    base: usize,
    p: Part,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    tick(c)?;
    let at = base
        .checked_add(parts.len())
        .ok_or("有限view構成位置が範囲外")?;
    parts.push(p);
    Ok(NodeRef(at))
}
fn value(
    parts: &mut Vec<Part>,
    base: usize,
    v: &Scalar,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        let mut children = vec![];
        let contains = super::path_value::contains_path(&v.ty(), c)?;
        if contains {
            match v {
                Scalar::Tuple(vs) | Scalar::List { items: vs, .. } => {
                    for v in vs {
                        children.push(value(parts, base, v, c)?);
                    }
                }
                Scalar::Option { value: Some(v), .. } => children.push(value(parts, base, v, c)?),
                Scalar::Option { value: None, .. } => (),
                _ => return Err("有限view域の非原始値を既出Refで表示できない".into()),
            }
        }
        let wire = if !contains {
            v.wire()
        } else {
            match v {
                Scalar::Tuple(_) | Scalar::List { .. } => refs(&children),
                Scalar::Option { value: None, .. } => Json::obj([("none", Json::Bool(true))]),
                Scalar::Option { value: Some(_), .. } => Json::obj([(
                    "some",
                    children.first().ok_or("有限viewのOption成分がない")?.wire(),
                )]),
                _ => return Err("有限view値の表示型が違う".into()),
            }
        };
        push(
            parts,
            base,
            Part::Value {
                scalar: v.clone(),
                children,
                wire,
            },
            c,
        )
    })
}
fn build_source(
    g: &Graph,
    a: Arc<ArchitectureWitness>,
    o: ViewOrigin,
    ps: Vec<Parameter>,
    base: usize,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    let mut parts = vec![];
    let mut domains = vec![];
    let mut axes = vec![];
    let mut support = g.get(o.expression)?.support.clone();
    let mut scope = g.get(o.architecture)?.scope.clone();
    scope.merge(&g.get(o.component)?.scope);
    for b in &o.bindings {
        support.extend(g.get(b.value)?.support.iter().cloned());
        scope.merge(&g.get(b.value)?.scope);
    }
    for p in &ps {
        tick(c)?;
        if !p.missing.is_empty() {
            return Err("有限view域の所属が欠測".into());
        }
        support.extend(p.support.iter().cloned());
        scope.merge(&p.scope);
        if symbolic(p) { continue; }
        let vs = p
            .values
            .as_ref()
            .ok_or("view parameter型が有限全域でない")?;
        let mut elements = vec![];
        for v in vs {
            if v.ty() != p.declaration.ty.erase() {
                return Err("有限view域の実値型が違う".into());
            }
            elements.push(value(&mut parts, base, v, c)?);
        }
        domains.push(push(
            &mut parts,
            base,
            Part::Domain {
                ty: p.declaration.ty.erase(),
                values: elements.clone(),
            },
            c,
        )?);
        axes.push(elements);
    }
    let mut keys = vec![vec![]];
    for axis in &axes {
        let mut next = vec![];
        for prefix in &keys {
            for r in axis {
                tick(c)?;
                let mut key = prefix.clone();
                key.push(*r);
                next.push(key);
            }
        }
        keys = next;
    }
    let types = ps
        .iter()
        .filter(|p| !symbolic(p))
        .map(|p| p.declaration.ty.erase())
        .collect::<Vec<_>>();
    let product_type = super::environment::family::family_type(&types);
    let mut members = vec![];
    for key in &keys {
        tick(c)?;
        let member = if key.len() == 1 {
            key[0]
        } else {
            let vs = key
                .iter()
                .map(|r| match parts.get(r.0 - base) {
                    Some(Part::Value { scalar, .. }) => Ok(scalar.clone()),
                    _ => Err("有限view直積の実値がない".into()),
                })
                .collect::<Result<Vec<_>, ValidationFailure>>()?;
            let scalar = Scalar::Tuple(vs);
            let wire = if super::path_value::contains_path(&scalar.ty(), c)? {
                refs(key)
            } else {
                scalar.wire()
            };
            push(
                &mut parts,
                base,
                Part::Value {
                    scalar,
                    children: key.clone(),
                    wire,
                },
                c,
            )?
        };
        members.push(member);
    }
    let product = push(
        &mut parts,
        base,
        Part::Domain {
            ty: product_type,
            values: members.clone(),
        },
        c,
    )?;
    let input = Witness::Architecture(a.clone());
    let declaration = input
        .inputs()
        .law()
        .declarations
        .get(&o.declaration)
        .ok_or("元view宣言がない")?;
    let Signature::View { params, .. } = &declaration.signature else {
        return Err("元宣言がviewでない".into());
    };
    let mut rows = vec![];
    for (key, member) in keys.iter().zip(members) {
        tick(c)?;
        let mut bindings = vec![];
        for p in params {
            let fixed = o
                .bindings
                .iter()
                .filter(|b| b.name == p.name)
                .collect::<Vec<_>>();
            if let [b] = fixed.as_slice() {
                bindings.push((*b).clone());
            } else if fixed.is_empty() {
                if numeric_parameters::numeric_width(&p.ty).is_some() { continue; }
                let i = ps
                    .iter()
                    .filter(|p| !symbolic(p))
                    .position(|x| x.declaration == *p)
                    .ok_or("具体viewの元parameter位置がない")?;
                bindings.push(Binding {
                    name: p.name.clone(),
                    ty: p.ty.erase(),
                    value: key[i],
                });
            } else {
                return Err("具体viewの固定束縛が重複する".into());
            }
        }
        let expression = NodeRef(base.checked_add(parts.len()).ok_or("view行位置が範囲外")?);
        let mut row = o.clone();
        row.expression = expression;
        row.parameters.retain(|(_, ty)| numeric_parameters::numeric_width(ty).is_some());
        row.bindings = bindings;
        rows.push(push(
            &mut parts,
            base,
            Part::Row {
                origin: row,
                member,
            },
            c,
        )?);
    }
    support.sort();
    support.dedup();
    Ok(Source {
        architecture: a,
        origin: o,
        parameters: ps,
        base,
        parts,
        domains,
        product,
        rows,
        support,
        scope,
    })
}
pub(super) fn validate_node(
    g: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let (a, o) = reading::origin(g, d.source.origin.expression)?;
    let Witness::Architecture(w) = &v.witness else {
        return Err("有限viewのArchitecture証拠がない".into());
    };
    if !Arc::ptr_eq(&a, w) || !Arc::ptr_eq(w, &d.source.architecture) || o != d.source.origin {
        return Err("有限viewの元式/Architectureが違う".into());
    }
    if n.ty != d.ty()
        || n.rule != Rule::Construction(d.construction())
        || n.arguments != d.arguments()
        || n.support != d.source.support
        || n.scope != d.source.scope
        || !n.reasons.is_empty()
        || !n.evidence.is_empty()
        || n.judgment.is_some()
    {
        return Err("有限view構成の型/辺/metadataが違う".into());
    }
    for r in d.part()?.refs() {
        if r.0 < d.source.base {
            if !d.source.origin.bindings.iter().any(|b| b.value == r) {
                return Err("具体view行に別の固定束縛がある".into());
            }
            continue;
        }
        let Some(Payload::Construction(child)) = &g.get(r)?.payload else {
            return Err("有限view構成の依存がnativeでない".into());
        };
        let D::ViewFamily(child) = &child.data else {
            return Err("有限view構成の依存が別構成".into());
        };
        child.position(r.0)?;
        if !Arc::ptr_eq(&child.source, &d.source) {
            return Err("有限view構成の依存が別族".into());
        }
    }
    if let Some(scalar) = d.scalar() {
        let wire = g.scalar_wire(scalar, &d.arguments())?;
        if wire != d.wire() {
            return Err("有限view値の既出Ref表示が違う".into());
        }
    }
    Ok(())
}
#[derive(Debug)]
pub(super) struct Family {
    pub domains: Vec<NodeRef>,
    pub product: NodeRef,
    pub expressions: Vec<NodeRef>,
    pub evaluations: Vec<NodeRef>,
    pub evaluation: NodeRef,
}
#[derive(Debug)]
pub(super) struct Pending {
    pub expression: NodeRef,
    pub parameters: Vec<Parameter>,
}
#[derive(Debug)]
pub(super) enum Outcome {
    Pending(Pending),
    Family(Family),
}
fn source_at(g: &Graph, r: NodeRef) -> Result<&Data, ValidationFailure> {
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("有限view族の実Domainがない".into());
    };
    let D::ViewFamily(d) = &v.data else {
        return Err("有限view族のDomainが別構成".into());
    };
    Ok(d)
}
fn family_node(g: &Graph, s: &Source, rows: &[NodeRef]) -> Result<Node, ValidationFailure> {
    if rows.len() != s.rows.len() {
        return Err("有限view族の全row評価がない".into());
    }
    let mut support = s.support.clone();
    let mut scope = s.scope.clone();
    scope.assignments = true;
    let mut reasons = vec![];
    for (p, r) in s.parameters.iter().filter(|p| !symbolic(p)).zip(&s.domains) {
        scope.quantifiers.push(Quantifier {
            kind: crate::law::ast::QuantKind::Forall,
            name: p.declaration.name.clone(),
            ty: p.declaration.ty.erase(),
            occurrence: p.declaration.span,
            domain: Some(*r),
            context: None,
        });
    }
    for (expression, r) in s.rows.iter().zip(rows) {
        let n = g.get(*r)?;
        let Some(Payload::Evaluation { expression: e, .. }) = &n.payload else {
            return Err("有限viewのrowが通常Evaluationでない".into());
        };
        if e != expression
            || n.ty != NodeType::Evaluation(s.origin.returns.clone())
            || g.context_at(r.0) != g.context_at(s.origin.expression.0)
        {
            return Err("有限view rowの元式/型/Contextが違う".into());
        }
        whole::validate(g, n, r.0)?;
        support.extend(n.support.iter().cloned());
        scope.merge(&n.scope);
        reasons.extend(n.reasons.iter().cloned());
    }
    support.sort();
    support.dedup();
    reasons.sort_by_key(|r| r.wire().canonical());
    reasons.dedup();
    let mut arguments = vec![s.origin.expression, s.origin.architecture];
    arguments.extend(&s.domains);
    arguments.push(s.product);
    arguments.extend(&s.rows);
    arguments.extend(rows);
    arguments.extend(s.origin.bindings.iter().map(|b| b.value));
    arguments.sort_by_key(|r| r.0);
    arguments.dedup();
    let witness = Witness::Architecture(s.architecture.clone());
    let location = Location::Law {
        span: witness
            .inputs()
            .law()
            .exprs
            .get(s.origin.body)
            .ok_or("元view bodyの出現がない")?
            .span,
    };
    Ok(Node {
        ty: NodeType::Evaluation(s.origin.returns.clone()),
        rule: Rule::Construction("evaluation"),
        arguments,
        support,
        scope,
        evidence: vec![],
        reasons,
        judgment: None,
        payload: Some(Payload::Evaluation {
            expression: s.origin.expression,
            bindings: s.origin.bindings.clone(),
            environment: Some(s.origin.architecture),
            parts: vec![PartResult {
                location,
                value: None,
                residual: None,
                children: rows.to_vec(),
            }],
            value: None,
            applicability: match &s.origin.application {
                crate::construction::readings::InstanceApplication::NotApplicable => {
                    "not_applicable"
                }
                crate::construction::readings::InstanceApplication::Applicable { conditions }
                    if !conditions.is_empty() =>
                {
                    "undetermined"
                }
                _ => "applicable",
            },
        }),
    })
}
// 部分構成のPartとEvaluationのAST出現を区別する。
type PartResult = super::result::Part;
pub(super) fn family_dependencies(
    g: &Graph,
    n: &Node,
) -> Result<Option<Vec<NodeRef>>, ValidationFailure> {
    let Some(Payload::Evaluation { expression, .. }) = &n.payload else {
        return Ok(None);
    };
    let Some(Payload::Construction(v)) = &g.get(*expression)?.payload else {
        return Ok(None);
    };
    let D::ObjectComponents(d) = &v.data else {
        return Ok(None);
    };
    let Some((_, o)) = d.view_origin(*expression)? else {
        return Ok(None);
    };
    if o.parameters.is_empty() {
        return Ok(None);
    }
    Ok(Some(whole::dependencies(g, n)?))
}
pub(super) fn validate_family(g: &Graph, n: &Node, at: usize) -> Result<(), ValidationFailure> {
    let Some(Payload::Evaluation {
        expression, parts, ..
    }) = &n.payload
    else {
        return Err("全view族が通常Evaluationでない".into());
    };
    if reading::numeric_parameters(&reading::origin(g, *expression)?.1)
        && !n.arguments.iter().any(|r| source_at(g, *r).is_ok_and(|d| *r == d.source.product)) {
        return whole::validate(g, n, at);
    }
    let [part] = parts.as_slice() else {
        return Err("全view族の元body出現がない".into());
    };
    let candidates = n
        .arguments
        .iter()
        .filter_map(|r| source_at(g, *r).ok().map(|d| (*r, d)))
        .filter(|(r, d)| *r == d.source.product)
        .collect::<Vec<_>>();
    let [(product, d)] = candidates.as_slice() else {
        return Err("全view族に唯一の元直積がない".into());
    };
    d.position(product.0)?;
    if d.source.origin.expression != *expression {
        return Err("全view族が別の元式".into());
    }
    if whole::dependencies(g, n)?.iter().any(|r| r.0 >= at) {
        return Err("全view族に自己未来Refがある".into());
    }
    let expected = family_node(g, &d.source, &part.children)?;
    if n != &expected {
        return Err("全view族の全row/順序/支持/Scope/式が違う".into());
    }
    Ok(())
}
pub(super) fn evaluate(
    env: &Environment<'_>,
    g: &mut Graph,
    expression: NodeRef,
    c: &mut Control,
) -> Result<Outcome, ValidationFailure> {
    tick(c)?;
    if g.active != g.context_at(expression.0) {
        return Err("有限view族の生成が元Request Contextでない".into());
    }
    env.recheck_node(g, g.get(expression)?, expression.0)?;
    let (a, o, ps) = parameters(env, g, expression, c)?;
    if pending_parameters(&ps) {
        return Ok(Outcome::Pending(Pending {
            expression,
            parameters: ps,
        }));
    }
    let source = Arc::new(build_source(g, a, o, ps, g.nodes.len(), c)?);
    for index in 0..source.parts.len() {
        tick(c)?;
        let d = Data {
            source: source.clone(),
            index,
        };
        d.position(g.nodes.len())?;
        native::retain(
            g,
            ConstructionValue {
                witness: Witness::Architecture(source.architecture.clone()),
                data: D::ViewFamily(d),
            },
            vec![],
            vec![],
            None,
        )?;
    }
    let mut evaluations = vec![];
    for r in &source.rows {
        tick(c)?;
        let whole::Outcome::Evaluation { evaluation, .. } = whole::evaluate(env, g, *r, c)? else {
            return Err("完全束縛view行にparameterが残る".into());
        };
        evaluations.push(evaluation);
    }
    tick(c)?;
    let n = family_node(g, &source, &evaluations)?;
    env.validate(g, &n)?;
    let evaluation = g.push(n)?;
    tick(c)?;
    Ok(Outcome::Family(Family {
        domains: source.domains.clone(),
        product: source.product,
        expressions: source.rows.clone(),
        evaluations,
        evaluation,
    }))
}
#[cfg(test)]
mod tests;
