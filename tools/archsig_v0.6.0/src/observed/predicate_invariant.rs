//! 元Law表の適用条件付き評価を、全対象の述語不変量へ接続する。
use super::{
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, Witness,
    },
    control::{Checkpoint, Control},
    environment::Environment,
    law_evaluation as frames,
    law_table::Table,
    object_component_diagram::Diagram as Objects,
    result::*,
};
use crate::{canonical::Json, issue::Location, law::model::Signature, types::Type};
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectEvaluation)?;
    Ok(())
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Part {
    ty: NodeType,
    construction: &'static str,
    wire: Json,
    arguments: Vec<NodeRef>,
    support: Vec<Fact>,
    scope: Scope,
    reasons: Vec<Reason>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Invariant {
    pub instance: usize,
    pub law: NodeRef,
    pub invariant: NodeRef,
    pub evaluations: Vec<NodeRef>,
}
#[derive(Clone, Debug)]
struct Source {
    architecture: Arc<ArchitectureWitness>,
    table: Arc<Table>,
    components: NodeRef,
    objects: Objects,
    base: usize,
    parts: Vec<Part>,
    outputs: Vec<Invariant>,
}
#[derive(Clone, Debug)]
pub(crate) struct Data {
    source: Arc<Source>,
    index: usize,
    part: Part,
}
impl PartialEq for Data {
    fn eq(&self, b: &Self) -> bool {
        Arc::ptr_eq(&self.source, &b.source) && self.index == b.index && self.part == b.part
    }
}
impl Eq for Data {}
fn components(
    g: &Graph,
    t: &Table,
) -> Result<(Arc<ArchitectureWitness>, NodeRef, Objects), ValidationFailure> {
    let r = t.component_source();
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("述語不変量の元対象表がnativeでない".into());
    };
    let D::ObjectComponents(d) = &v.data else {
        return Err("述語不変量の元対象表が別構成".into());
    };
    d.position(r.0)?;
    let (a, reference, objects) = d.retained_components();
    if reference != t.architecture
        || r != objects.base
        || !Arc::ptr_eq(&a, native::architecture_origin(g, reference, 0)?)
    {
        return Err("述語不変量の元全対象/Architectureが違う".into());
    }
    Ok((a, r, objects))
}
fn metadata(
    g: &Graph,
    arguments: &[NodeRef],
    c: &mut Control,
) -> Result<(Vec<Fact>, Scope, Vec<Reason>), ValidationFailure> {
    let mut support = vec![];
    let mut scope = Scope::default();
    let mut reasons = vec![];
    for r in arguments {
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
    Ok((support, scope, reasons))
}
fn refs(rs: &[NodeRef]) -> Json {
    Json::Arr(rs.iter().copied().map(NodeRef::wire).collect())
}
fn parameter_wire(ps: &[(String, Type)]) -> Json {
    Json::Arr(
        ps.iter()
            .map(|(n, t)| Json::obj([("name", Json::str(n)), ("type", t.wire())]))
            .collect(),
    )
}
fn bindings_wire(bs: &[Binding]) -> Json {
    Json::Arr(
        bs.iter()
            .map(|b| Json::obj([("name", Json::str(&b.name)), ("value", b.value.wire())]))
            .collect(),
    )
}
fn evaluation_parts(
    g: &Graph,
    e: NodeRef,
    parameters: bool,
) -> Result<(Option<NodeRef>, &'static str, Vec<NodeRef>), ValidationFailure> {
    let (value, app, children) = match &g.get(e)?.payload {
        Some(Payload::Evaluation {
            value,
            applicability,
            ..
        }) if !parameters => (*value, *applicability, vec![e]),
        Some(Payload::Construction(v)) => match &v.data {
            D::OutsideLaw(d) if !parameters => match &d.kind {
                super::law_inapplicable::Kind::Evaluation { value } => {
                    (Some(*value), "not_applicable", vec![e])
                }
                _ => return Err("述語読取りの非適用評価が別種".into()),
            },
            D::LawFamily(d) if parameters => match &d.kind {
                super::law_family::Kind::Evaluation { rows, .. } => (
                    None,
                    "applicable",
                    rows.iter().map(|r| r.evaluation).collect(),
                ),
                _ => return Err("述語読取りの全parameter評価が別種".into()),
            },
            _ => return Err("述語読取りの元評価が別構成/parameter署名".into()),
        },
        _ => return Err("述語読取りの元Evaluationがない".into()),
    };
    if let Some(value) = value {
        g.expect(value, &NodeType::Value(Type::Bool))?;
    }
    // 全parameterの関数は各rowを直接保持し、全称集計Boolを単一値として出さない。
    Ok((value, app, children))
}

fn compute(
    env: &Environment<'_>,
    g: &Graph,
    a: &Arc<ArchitectureWitness>,
    t: &Table,
    component: NodeRef,
    objects: &Objects,
    base: usize,
    c: &mut Control,
) -> Result<(Vec<Part>, Vec<Invariant>), ValidationFailure> {
    tick(c)?;
    let ds = t.diagrams()?;
    let first = ds.first().ok_or("述語不変量に元Law計画がない")?;
    let templates = first
        .originals
        .iter()
        .filter(|o| o.row.is_none())
        .collect::<Vec<_>>();
    if templates.len() != t.indices.len()
        || t.objects.len() != objects.objects.len()
        || objects.objects.is_empty()
    {
        return Err("述語不変量の全Law/全対象coverageが違う".into());
    }
    let mut parts = vec![];
    let mut outputs = vec![];
    for (column, original) in templates.iter().enumerate() {
        tick(c)?;
        let row = a
            .readings()
            .instances()
            .get(original.instance)
            .ok_or("述語不変量の元instanceがない")?;
        if row.declaration().kind != "law" || t.indices[column] != original.reference {
            return Err("述語不変量の元Law instance/順序が違う".into());
        }
        let owner = Witness::Architecture(a.clone());
        let declaration = owner
            .inputs()
            .law()
            .declarations
            .get(&row.declaration().name)
            .ok_or("述語不変量の元宣言がない")?;
        let Signature::Law { body, .. } = &declaration.signature else {
            return Err("述語不変量の元宣言がLawでない".into());
        };
        let parameters = row
            .parameters()
            .iter()
            .map(|p| (p.name.clone(), p.ty.erase()))
            .collect::<Vec<_>>();
        if parameters != original.parameters {
            return Err("述語不変量の元残parameter署名が違う".into());
        }
        let mut values = vec![];
        let mut evaluations = vec![];
        let mut dependencies = vec![component, t.architecture, t.indices[column]];
        let mut support = vec![];
        let mut scope = Scope::default();
        let mut reasons = vec![];
        for (object, cells) in t.objects.iter().enumerate() {
            tick(c)?;
            let rs = objects
                .readings
                .iter()
                .filter(|r| r.instance == original.instance && r.object == object)
                .collect::<Vec<_>>();
            let [source] = rs.as_slice() else {
                return Err("述語不変量の対象の元object_readingが一つでない".into());
            };
            let n = g.get(source.expression)?;
            env.recheck_node(g, n, source.expression.0)?;
            g.expect(source.expression, &NodeType::Expression(Type::Bool))?;
            let origin = frames::origin(g, cells.origins[column])?
                .ok_or("述語不変量の元Law評価由来がない")?;
            if origin.object != object
                || origin.declaration != row.declaration().name
                || !Arc::ptr_eq(&origin.architecture, a)
                || objects.objects.get(object) != Some(&cells.object)
                || objects.architectures.get(object) != Some(&cells.architecture)
            {
                return Err("述語不変量の対象/宣言/元評価が違う".into());
            }
            // object_reading自身は封印された元対象表にあり、元Law表の参照束縛と照合する。
            let Some(Payload::Construction(v)) = &n.payload else {
                return Err("述語の元式がnativeでない".into());
            };
            let D::ObjectComponents(d) = &v.data else {
                return Err("述語の元式が元対象表にない".into());
            };
            let (component_owner, reference, actual) = d.retained_components();
            if !Arc::ptr_eq(&component_owner, a)
                || reference != t.architecture
                || actual != *objects
            {
                return Err("述語の元式が別対象表".into());
            }
            if origin.bindings.len() != original.bindings.len() {
                return Err("述語の元固定束縛数が違う".into());
            }
            for (x, y) in origin.bindings.iter().zip(&original.bindings) {
                tick(c)?;
                if x.name != y.name || x.ty != y.ty || g.scalar(x.value)? != g.scalar(y.value)? {
                    return Err("述語の元固定束縛が違う".into());
                }
            }
            let (value, applicability, children) =
                evaluation_parts(g, cells.evaluations[column], !parameters.is_empty())?;
            let applicability = if origin.outside {
                "not_applicable"
            } else {
                applicability
            };
            let mut arguments = vec![
                component,
                t.indices[column],
                cells.object,
                cells.architecture,
                source.expression,
                cells.origins[column],
                cells.evaluations[column],
                cells.holds[column],
            ];
            arguments.extend(children.iter().copied());
            arguments.extend(origin.bindings.iter().map(|b| b.value));
            if let Some(v) = value {
                arguments.push(v);
            }
            arguments.sort_by_key(|r| r.0);
            arguments.dedup();
            let (facts, s, why) = metadata(g, &arguments, c)?;
            let mut fields = vec![
                ("expression", source.expression.wire()),
                ("bindings", bindings_wire(&origin.bindings)),
                ("environment", cells.architecture.wire()),
                ("applicability", Json::str(applicability)),
                (
                    "parts",
                    Json::Arr(vec![Json::obj([
                        (
                            "location",
                            crate::result::location_wire(&Location::Law {
                                span: owner.inputs().law().exprs[*body].span,
                            }),
                        ),
                        ("children", refs(&children)),
                    ])]),
                ),
            ];
            if let Some(v) = value {
                fields.push(("value", v.wire()));
            }
            let evaluation = NodeRef(
                base.checked_add(parts.len())
                    .ok_or("述語の生成位置が域外")?,
            );
            parts.push(Part {
                ty: NodeType::Evaluation(Type::Bool),
                construction: "evaluation",
                wire: Json::Obj(
                    fields
                        .into_iter()
                        .map(|(k, v)| (k.to_string(), v))
                        .collect(),
                ),
                arguments: arguments.clone(),
                support: facts.clone(),
                scope: s.clone(),
                reasons: why.clone(),
            });
            dependencies.extend(arguments);
            dependencies.push(evaluation);
            support.extend(facts);
            scope.merge(&s);
            reasons.extend(why);
            evaluations.push(evaluation);
            values.push(Json::obj([
                ("object", cells.object.wire()),
                ("expression", source.expression.wire()),
                ("evaluation", evaluation.wire()),
            ]));
        }
        dependencies.sort_by_key(|r| r.0);
        dependencies.dedup();
        support.sort();
        support.dedup();
        reasons.sort_by_key(|r| r.wire().canonical());
        reasons.dedup();
        let invariant = NodeRef(
            base.checked_add(parts.len())
                .ok_or("述語不変量の生成位置が域外")?,
        );
        parts.push(Part {
            ty: NodeType::Construction(T::Invariant),
            construction: "invariant",
            wire: Json::obj([
                ("kind", Json::str("predicate")),
                ("instance", original.reference.wire()),
                ("parameters", parameter_wire(&parameters)),
                ("values", Json::Arr(values)),
            ]),
            arguments: dependencies,
            support,
            scope,
            reasons,
        });
        outputs.push(Invariant {
            instance: original.instance,
            law: original.reference,
            invariant,
            evaluations,
        });
    }
    tick(c)?;
    Ok((parts, outputs))
}
impl Data {
    pub(super) fn ty(&self) -> NodeType {
        self.part.ty.clone()
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part.construction
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        self.part.arguments.clone()
    }
    pub(super) fn wire(&self) -> Json {
        self.part.wire.clone()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.part.support.clone(), self.part.scope.clone())
    }
    pub(super) fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        if self.source.base.checked_add(self.index) != Some(at)
            || self.arguments().iter().any(|r| r.0 >= at)
        {
            return Err("述語不変量の元生成位置/既出Refが違う".into());
        }
        Ok(())
    }
    fn node(&self) -> Node {
        Node {
            ty: self.ty(),
            rule: Rule::Construction(self.construction()),
            arguments: self.arguments(),
            support: self.part.support.clone(),
            scope: self.part.scope.clone(),
            reasons: self.part.reasons.clone(),
            evidence: vec![],
            judgment: None,
            payload: Some(Payload::Construction(Box::new(ConstructionValue {
                witness: Witness::Architecture(self.source.architecture.clone()),
                data: D::PredicateInvariant(self.clone()),
            }))),
        }
    }
}
pub(super) fn retain(
    env: &Environment<'_>,
    g: &mut Graph,
    t: Arc<Table>,
    c: &mut Control,
) -> Result<Vec<Invariant>, ValidationFailure> {
    tick(c)?;
    if g.active != g.context_at(t.architecture.0) {
        return Err("述語不変量の生成が元Request Contextでない".into());
    }
    t.recheck(env, g, c)?;
    let (a, components, objects) = components(g, &t)?;
    let base = g.nodes.len();
    let (parts, outputs) = compute(env, g, &a, &t, components, &objects, base, c)?;
    let source = Arc::new(Source {
        architecture: a,
        table: t,
        components,
        objects,
        base,
        parts,
        outputs,
    });
    for (index, part) in source.parts.iter().enumerate() {
        tick(c)?;
        let data = Data {
            source: source.clone(),
            index,
            part: part.clone(),
        };
        data.position(g.nodes.len())?;
        // 元表を再検査し全Partを導出済み。封印済みnative値の通常転記を使う。
        g.retain_native(data.node())?;
    }
    tick(c)?;
    Ok(source.outputs.clone())
}
pub(super) fn validate_node(
    g: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let Witness::Architecture(a) = &v.witness else {
        return Err("述語不変量のconsumerが別種".into());
    };
    if !Arc::ptr_eq(a, &d.source.architecture)
        || d.source.parts.get(d.index) != Some(&d.part)
        || n != &d.node()
        || &d.node() != n
    {
        return Err("述語不変量の元由来/全対象/metadataが違う".into());
    }
    for r in d.arguments() {
        g.get(r)?;
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_predicate_invariant(
        &self,
        g: &Graph,
        v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        let D::PredicateInvariant(d) = &v.data else {
            return Ok(());
        };
        d.position(at)?;
        let mut c = self.control.clone();
        d.source.table.recheck(self, g, &mut c)?;
        let (a, components, objects) = components(g, &d.source.table)?;
        if !Arc::ptr_eq(&a, &d.source.architecture)
            || components != d.source.components
            || objects != d.source.objects
        {
            return Err("述語不変量の元入力/対象表が違う".into());
        }
        let (parts, outputs) = compute(
            self,
            g,
            &a,
            &d.source.table,
            components,
            &objects,
            d.source.base,
            &mut c,
        )?;
        if parts != d.source.parts || outputs != d.source.outputs {
            return Err("述語不変量の元全Law/全域評価/metadataが違う".into());
        }
        Ok(())
    }
}
#[cfg(test)]
#[path = "predicate_invariant_tests.rs"]
mod tests;
