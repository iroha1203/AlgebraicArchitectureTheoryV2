//! 再検査済みの全Law表と共有表示を、一つのEquationFamilyへ保持する。
use super::{
    construction_result as native,
    construction_result::{
        ArchitectureWitness, ConstructionData as D, ConstructionType as T, ConstructionValue,
        Witness,
    },
    environment::Environment,
    observable_layout::{Layout, Source as CoordinateSource},
    result::*,
};
use crate::control::{Checkpoint, Control};
use crate::canonical::Json;
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::EquationPresentation)?;
    Ok(())
}
fn refs(rs: &[NodeRef]) -> Json {
    Json::Arr(rs.iter().copied().map(NodeRef::wire).collect())
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Coordinate {
    instance: NodeRef,
    component: Vec<usize>,
    factor: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Object {
    object: NodeRef,
    evaluations: Vec<NodeRef>,
    holds: Vec<NodeRef>,
    presentations: Vec<NodeRef>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Output {
    indices: Vec<NodeRef>,
    factors: Vec<NodeRef>,
    universe: NodeRef,
    anchor: Fact,
    coordinates: Vec<Coordinate>,
    objects: Vec<Object>,
}
impl Output {
    fn arguments(&self, architecture: NodeRef) -> Vec<NodeRef> {
        let mut rs = vec![architecture, self.universe];
        rs.extend(self.indices.iter().copied());
        rs.extend(self.factors.iter().copied());
        rs.extend(self.coordinates.iter().map(|q| q.instance));
        for row in &self.objects {
            rs.push(row.object);
            rs.extend(row.evaluations.iter().copied());
            rs.extend(row.holds.iter().copied());
            rs.extend(row.presentations.iter().copied());
        }
        rs.sort_by_key(|r| r.0);
        rs.dedup();
        rs
    }
    fn wire(&self) -> Json {
        Json::obj([
            ("indices", refs(&self.indices)),
            ("observable_factors", refs(&self.factors)),
            (
                "embedding",
                Json::obj([
                    ("universe", self.universe.wire()),
                    ("anchor", self.anchor.wire()),
                    (
                        "coordinates",
                        Json::Arr(
                            self.coordinates
                                .iter()
                                .map(|q| {
                                    Json::obj([
                                        ("instance", q.instance.wire()),
                                        (
                                            "component",
                                            Json::Arr(
                                                q.component
                                                    .iter()
                                                    .map(|&n| Json::Nat(n as u64))
                                                    .collect(),
                                            ),
                                        ),
                                        ("factor", Json::Nat(q.factor as u64)),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                ]),
            ),
            (
                "objects",
                Json::Arr(
                    self.objects
                        .iter()
                        .map(|o| {
                            Json::obj([
                                ("object", o.object.wire()),
                                ("evaluations", refs(&o.evaluations)),
                                ("holds", refs(&o.holds)),
                                ("presentations", refs(&o.presentations)),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
    }
}
#[derive(Clone, Debug)]
struct Source {
    layout: Arc<Layout>,
    architecture: Arc<ArchitectureWitness>,
    position: usize,
    output: Output,
}
#[derive(Clone, Debug)]
pub(crate) struct Data {
    source: Arc<Source>,
    output: Output,
}
impl PartialEq for Data {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.source, &other.source) && self.output == other.output
    }
}
impl Eq for Data {}
fn output(layout: &Layout, c: &mut Control) -> Result<Option<Output>, ValidationFailure> {
    tick(c)?;
    if !layout.data.complete {
        return Ok(None);
    }
    let table = layout.law_table();
    let base = layout
        .data
        .objects
        .first()
        .ok_or("EquationFamilyのbase対象がない")?;
    let mut coordinates = vec![];
    for q in &base.coordinates {
        tick(c)?;
        let (instance, component) = match &q.source {
            CoordinateSource::Polynomial(q) => (q.instance, q.component.clone()),
            CoordinateSource::Finite(q) => (q.value.instance, q.value.component.clone()),
        };
        let factor = q.factor.ok_or("EquationFamilyの座標factorが未生成")?;
        if coordinates
            .iter()
            .any(|p: &Coordinate| p.instance == instance && p.component == component)
        {
            return Err("EquationFamilyの元instance/component座標が重複".into());
        }
        coordinates.push(Coordinate {
            instance,
            component,
            factor,
        });
    }
    let mut objects = vec![];
    for (row, placement) in table.objects.iter().zip(&layout.data.objects) {
        tick(c)?;
        let presentations = placement
            .presentations
            .iter()
            .copied()
            .collect::<Option<Vec<_>>>()
            .ok_or("EquationFamilyの型別表示が未生成")?;
        objects.push(Object {
            object: row.object,
            evaluations: row.evaluations.clone(),
            holds: row.holds.clone(),
            presentations,
        });
    }
    tick(c)?;
    Ok(Some(Output {
        indices: table.indices.clone(),
        factors: layout.data.factors.clone(),
        universe: layout.data.universe,
        anchor: layout.data.anchor.clone(),
        coordinates,
        objects,
    }))
}
impl Data {
    pub(super) fn ty(&self) -> NodeType {
        NodeType::Construction(T::EquationFamily)
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        self.output.arguments(self.source.layout.data.architecture)
    }
    pub(super) fn wire(&self) -> Json {
        self.output.wire()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (
            self.source.layout.data.support.clone(),
            self.source.layout.data.scope.clone(),
        )
    }
    pub(super) fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        if at != self.source.position || self.arguments().iter().any(|r| r.0 >= at) {
            return Err("EquationFamilyの生成位置/既出参照が違う".into());
        }
        Ok(())
    }
}
pub(super) fn retain(
    env: &Environment<'_>,
    g: &mut Graph,
    layout: Arc<Layout>,
    c: &mut Control,
) -> Result<Option<NodeRef>, ValidationFailure> {
    tick(c)?;
    if g.active != g.context_at(layout.data.architecture.0) {
        return Err("EquationFamilyの生成が元ArchitectureのRequestでない".into());
    }
    layout.recheck(env, g, c)?;
    let Some(output) = output(&layout, c)? else {
        return Ok(None);
    };
    let a = native::architecture_origin(g, layout.data.architecture, 0)?.clone();
    let source = Arc::new(Source {
        layout,
        architecture: a.clone(),
        position: g.nodes.len(),
        output: output.clone(),
    });
    let data = Data { source, output };
    data.position(g.nodes.len())?;
    tick(c)?;
    let reference = native::retain(
        g,
        ConstructionValue {
            witness: Witness::Architecture(a),
            data: D::EquationFamily(data),
        },
        vec![],
        vec![],
        None,
    )?;
    tick(c)?;
    Ok(Some(reference))
}
pub(super) fn validate_node(g: &Graph, n: &Node, data: &Data) -> Result<(), ValidationFailure> {
    let Some(Payload::Construction(value)) = &n.payload else {
        return Err("EquationFamilyのnative値がない".into());
    };
    let Witness::Architecture(a) = &value.witness else {
        return Err("EquationFamilyの元Architectureがない".into());
    };
    let current = native::architecture_origin(g, data.source.layout.data.architecture, 0)?;
    let (support, scope) = data.metadata();
    if !Arc::ptr_eq(a, current)
        || !Arc::ptr_eq(a, &data.source.architecture)
        || data.output != data.source.output
        || n.ty != data.ty()
        || n.rule != Rule::Construction("equation_family")
        || n.arguments != data.arguments()
        || n.support != support
        || n.scope != scope
        || !n.reasons.is_empty()
        || !n.evidence.is_empty()
        || n.judgment.is_some()
    {
        return Err("EquationFamilyの元計画/型/辺/metadata/判断が違う".into());
    }
    for r in data.arguments() {
        g.tick()?;
        g.get(r)?;
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_equation_family(
        &self,
        g: &Graph,
        value: &ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        let D::EquationFamily(data) = &value.data else {
            return Ok(());
        };
        let Witness::Architecture(a) = &value.witness else {
            return Err("EquationFamilyのconsumerが別種".into());
        };
        let current = native::architecture_origin(g, data.source.layout.data.architecture, 0)?;
        if !Arc::ptr_eq(a, current) || !Arc::ptr_eq(a, &data.source.architecture) {
            return Err("EquationFamilyのconsumerが元Architectureと違う".into());
        }
        let mut c = self.control.clone();
        data.source.layout.recheck(self, g, &mut c)?;
        if output(&data.source.layout, &mut c)?.as_ref() != Some(&data.source.output) {
            return Err("EquationFamilyの全添字/対象/座標が元計画と違う".into());
        }
        tick(&mut c)
    }
}
#[cfg(test)]
#[path = "equation_family_tests.rs"]
mod tests;
