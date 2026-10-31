//! 全内部arrowの元候補と、保存確認済みの生成操作を実対象族へ接続する。
use super::{
    construction_result as native,
    construction_result::{
        ArchitectureWitness, ConstructionData as D, ConstructionType as T, ConstructionValue,
        Witness,
    },
    environment::Environment,
    object_component_diagram as objects,
    object_component_diagram::Diagram as Objects,
    result::*,
};
use crate::{
    canonical::Json,
    construction::{
        ConstructionFailure,
        maps::{ConfigurationOperation, InternalArrows, internal_arrows},
    },
};
use crate::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
};
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::InternalArrow)?;
    Ok(())
}
fn failure(e: ConstructionFailure) -> ValidationFailure {
    match e {
        ConstructionFailure::Stopped(s) => s.into(),
        e => format!("内部arrowのnative接続: {e:?}").into(),
    }
}
fn refs(rs: &[NodeRef]) -> Json {
    Json::Arr(rs.iter().map(|r| r.wire()).collect())
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Part {
    Subject(Scalar),
    Action {
        universe: NodeRef,
        images: Vec<Fact>,
    },
    Candidate {
        declaration: String,
        subject: NodeRef,
        source: NodeRef,
        target: NodeRef,
        action: NodeRef,
    },
    Evidence {
        subject: NodeRef,
        left: NodeRef,
        right: NodeRef,
        facts: Vec<Fact>,
    },
    Map {
        candidate: NodeRef,
    },
    Operation {
        kernel: Box<ConfigurationOperation>,
        subject: NodeRef,
        source: NodeRef,
        target: NodeRef,
        candidate: NodeRef,
        map: NodeRef,
        action: NodeRef,
    },
}
impl Part {
    fn ty(&self) -> NodeType {
        NodeType::Construction(match self {
            Self::Subject(v) => return NodeType::Value(v.ty()),
            Self::Evidence { .. } => return NodeType::Evidence,
            Self::Action { .. } => T::AtomMap,
            Self::Candidate { .. } => T::MapCandidate,
            Self::Map { .. } => T::ConfigurationMap,
            Self::Operation { .. } => T::Operation,
        })
    }
    fn construction(&self) -> &'static str {
        match self {
            Self::Subject(_) => "binding",
            Self::Action { .. } => "atom_map",
            Self::Candidate { .. } => "map_candidate",
            Self::Evidence { .. } => "evidence",
            Self::Map { .. } => "configuration_map",
            Self::Operation { .. } => "operation",
        }
    }
    fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Subject(_) => vec![],
            Self::Action { universe, .. } => vec![*universe],
            Self::Candidate {
                subject,
                source,
                target,
                action,
                ..
            } => vec![*subject, *source, *target, *action],
            Self::Evidence {
                subject,
                left,
                right,
                ..
            } => vec![*subject, *left, *right],
            Self::Map { candidate } => vec![*candidate],
            Self::Operation {
                subject,
                source,
                target,
                candidate,
                map,
                action,
                ..
            } => vec![*subject, *source, *target, *candidate, *map, *action],
        }
    }
    fn wire(&self) -> Json {
        match self {
            Self::Subject(v) => v.wire(),
            Self::Action { universe, images } => Json::obj([
                ("universe", universe.wire()),
                ("images", Json::Arr(images.iter().map(Fact::wire).collect())),
            ]),
            Self::Candidate {
                declaration,
                subject,
                source,
                target,
                action,
            } => Json::obj([
                ("declaration", Json::str(declaration)),
                ("subject", subject.wire()),
                ("source", source.wire()),
                ("target", target.wire()),
                ("action", action.wire()),
            ]),
            Self::Evidence {
                subject,
                left,
                right,
                facts,
            } => Json::obj([
                ("kind", Json::str("counterexample")),
                (
                    "data",
                    Json::obj([
                        (
                            "bindings",
                            Json::Arr(vec![Json::obj([
                                ("name", Json::str("on")),
                                ("value", subject.wire()),
                            ])]),
                        ),
                        ("paths", Json::Arr(vec![])),
                        ("left", left.wire()),
                        ("right", right.wire()),
                        ("facts", Json::Arr(facts.iter().map(Fact::wire).collect())),
                    ]),
                ),
            ]),
            Self::Map { candidate } => Json::obj([("candidate", candidate.wire())]),
            Self::Operation {
                subject,
                source,
                target,
                candidate,
                map,
                action,
                ..
            } => Json::obj([
                ("source", source.wire()),
                ("target", target.wire()),
                ("candidate", candidate.wire()),
                ("configuration_map", map.wire()),
                ("action", action.wire()),
                (
                    "name",
                    Json::obj([
                        ("kind", Json::str("generator")),
                        ("subject", subject.wire()),
                    ]),
                ),
                ("word", refs(&[*subject])),
            ]),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Row {
    pub subject: NodeRef,
    pub candidate: Option<NodeRef>,
    pub evidence: Vec<NodeRef>,
    pub missing: Vec<Fact>,
    pub operation: Option<NodeRef>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Diagram {
    pub rows: Vec<Row>,
    pub all_preserved: bool,
}
#[derive(Clone)]
pub(super) struct Source {
    inputs: Arc<CheckedInputs>,
    architecture: Arc<ArchitectureWitness>,
    reference: NodeRef,
    objects: Objects,
    universe: NodeRef,
    base: usize,
    core: InternalArrows,
    parts: Vec<Part>,
    outputs: Diagram,
    support: Vec<Fact>,
    scope: Scope,
}
impl std::fmt::Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InternalArrowSource")
            .field("reference", &self.reference)
            .field("base", &self.base)
            .finish()
    }
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
    fn part(&self) -> &Part {
        &self.source.parts[self.index]
    }
    pub(super) fn projection_type(&self) -> Option<super::projection::ProjectionType> {
        use super::projection::{MapProjection, ProjectionType as P};
        let part = self.source.parts.get(self.index)?;
        if matches!(part, Part::Action { .. }) {
            return Some(P::AtomMap);
        }
        let candidate = match part {
            Part::Candidate { .. } => part,
            Part::Map { candidate } | Part::Operation { candidate, .. } => self
                .source
                .parts
                .get(candidate.0.checked_sub(self.source.base)?)?,
            _ => return None,
        };
        let Part::Candidate {
            declaration,
            source,
            target,
            ..
        } = candidate
        else {
            return None;
        };
        let entity = |reference: NodeRef| -> Option<String> {
            let index = self
                .source
                .objects
                .architectures
                .iter()
                .position(|r| *r == reference)?;
            let identity = self
                .source
                .architecture
                .readings()
                .objects()
                .get(index)?
                .identity()
                .subject();
            Some(
                self.source
                    .inputs
                    .archmap()
                    .snapshots
                    .iter()
                    .find(|s| s.id == identity.snapshot)?
                    .subjects
                    .iter()
                    .find(|s| s.id == identity.subject)?
                    .ty
                    .clone(),
            )
        };
        let shape = MapProjection {
            declaration: declaration.clone(),
            source: entity(*source)?,
            target: entity(*target)?,
        };
        Some(match part {
            Part::Candidate { .. } => P::MapCandidate(shape),
            Part::Map { .. } => P::ConfigurationMap(shape),
            Part::Operation { .. } => P::Operation(shape),
            _ => return None,
        })
    }
    /// 既出nodeの再検査後に、保持した同じ核のOperationを消費する。
    pub(super) fn operation(&self) -> Option<&ConfigurationOperation> {
        match self.source.parts.get(self.index)? {
            Part::Operation { kernel, .. } => Some(kernel),
            _ => None,
        }
    }
    pub(super) fn components(&self) -> Option<(NodeRef, NodeRef, NodeRef, Vec<NodeRef>)> {
        match self.source.parts.get(self.index)? {
            Part::Operation {
                subject,
                source,
                target,
                action,
                ..
            } => Some((*source, *target, *action, vec![*subject])),
            _ => None,
        }
    }
    pub(super) fn universe(&self) -> Option<NodeRef> {
        match self.source.parts.get(self.index)? {
            Part::Action { universe, .. } => Some(*universe),
            _ => None,
        }
    }
    pub(super) fn project(
        &self,
        path: &[super::projection::ProjectionStep],
    ) -> Option<(NodeRef, usize)> {
        use super::projection::ProjectionStep as P;
        let P::Field(field) = path.first()? else {
            return None;
        };
        let part = self.source.parts.get(self.index)?;
        let reference = match (part, field.as_str()) {
            (Part::Candidate { subject, .. }, "subject") => *subject,
            (Part::Candidate { source, .. } | Part::Operation { source, .. }, "source") => *source,
            (Part::Candidate { target, .. } | Part::Operation { target, .. }, "target") => *target,
            (Part::Candidate { action, .. } | Part::Operation { action, .. }, "action") => *action,
            (Part::Map { candidate } | Part::Operation { candidate, .. }, "candidate") => {
                *candidate
            }
            (Part::Operation { map, .. }, "configuration_map") => *map,
            (Part::Operation { subject, .. }, "word") if path.get(1) == Some(&P::Index(0)) => {
                return Some((*subject, 2));
            }
            _ => return None,
        };
        Some((reference, 1))
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        match self.source.parts.get(self.index) {
            Some(Part::Subject(v)) => Some(v),
            _ => None,
        }
    }
    pub(super) fn ty(&self) -> NodeType {
        self.part().ty()
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part().construction()
    }
    pub(super) fn wire(&self) -> Json {
        self.part().wire()
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        [
            self.source.reference,
            self.source.objects.base,
            self.source.universe,
        ]
        .into_iter()
        .chain(self.part().arguments())
        .collect()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.source.support.clone(), self.source.scope.clone())
    }
    pub(super) fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        if self.index >= self.source.parts.len()
            || self.source.base.checked_add(self.index) != Some(at)
        {
            return Err("内部arrowの生成位置が元計画と違う".into());
        }
        Ok(())
    }
}
fn push(
    parts: &mut Vec<Part>,
    base: usize,
    part: Part,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    tick(c)?;
    let at = base
        .checked_add(parts.len())
        .ok_or("内部arrowの生成番号が範囲外")?;
    parts.push(part);
    Ok(NodeRef(at))
}
fn original<'a>(
    graph: &'a Graph,
    reference: NodeRef,
    base: NodeRef,
    universe: NodeRef,
) -> Result<(&'a Arc<ArchitectureWitness>, Objects), ValidationFailure> {
    let Some(Payload::Construction(v)) = &graph.get(reference)?.payload else {
        return Err("内部arrowの元Architectureがない".into());
    };
    let (Witness::Architecture(a), D::Architecture { .. }) = (&v.witness, &v.data) else {
        return Err("内部arrowの元Architectureが完成構成でない".into());
    };
    let context = graph.context_at(reference.0);
    if context.frame.is_some()
        || context.iteration.is_some()
        || context.instance.is_some()
        || context.case.is_some()
        || graph.requests.get(context.request) != Some(Witness::Architecture(a.clone()).request())
    {
        return Err("内部arrowの元Requestが違う".into());
    }
    let (owner, objects) = objects::original_family(graph, base)?;
    if owner != reference {
        return Err("内部arrowの対象表が別Architectureに属する".into());
    }
    let Some(Payload::Construction(u)) = &graph.get(universe)?.payload else {
        return Err("内部arrowのUがnativeでない".into());
    };
    if !matches!(&u.data,D::AtomUniverse(atoms) if atoms==a.construction().universe()) {
        return Err("内部arrowのUが元共有集合でない".into());
    }
    Ok((a, objects))
}
fn plan(
    inputs: &CheckedInputs,
    a: &ArchitectureWitness,
    objects: &Objects,
    universe: NodeRef,
    base: usize,
    core: &InternalArrows,
    c: &mut Control,
) -> Result<(Vec<Part>, Diagram), ValidationFailure> {
    if !core.is_complete() || core.construction() != a.construction() {
        return Err("内部arrowの元構成または全件検査が違う".into());
    }
    let mut parts = vec![];
    let mut rows = vec![];
    let endpoint = |identity: &crate::construction::maps::ObjectIdentity| -> Result<NodeRef, ValidationFailure> {
        if identity.root() != a.construction().root()
            || identity.reading() != a.construction().reading()
        {
            return Err("内部arrowの包含root・readingが違う".into());
        }
        let index = a.readings().objects().iter()
            .position(|o| o.identity() == identity)
            .ok_or("内部arrowの端点が元対象表にない")?;
        objects.architectures.get(index).copied()
            .ok_or_else(|| "内部arrowの実Architectureがない".into())
    };
    for row in core.arrows() {
        tick(c)?;
        let f = row.arrow();
        let original = inputs
            .archmap()
            .snapshots
            .iter()
            .find(|s| s.id == f.snapshot)
            .and_then(|s| s.subjects.iter().find(|s| s.id == f.subject))
            .ok_or("内部arrowの原始subjectがない")?;
        let subject = push(
            &mut parts,
            base,
            Part::Subject(Scalar::Subject {
                snapshot: f.snapshot.clone(),
                subject: f.subject.clone(),
                entity: original.ty.clone(),
            }),
            c,
        )?;
        let mut candidate_ref = None;
        let mut operation = None;
        if let Some(candidate) = row.candidate() {
            if candidate.universe() != a.construction().universe()
                || candidate.subject() != Some(row.arrow())
                || candidate.images().len() != candidate.universe().len()
            {
                return Err("内部arrowの元候補・総作用が違う".into());
            }
            let source = endpoint(&candidate.source_object())?;
            let target = endpoint(&candidate.target_object())?;
            let action = push(
                &mut parts,
                base,
                Part::Action {
                    universe,
                    images: candidate.images().to_vec(),
                },
                c,
            )?;
            let candidate = push(
                &mut parts,
                base,
                Part::Candidate {
                    declaration: original.ty.clone(),
                    subject,
                    source,
                    target,
                    action,
                },
                c,
            )?;
            candidate_ref = Some(candidate);
            if let Some(map) = row.map() {
                let op = ConfigurationOperation::from_map(inputs, map, c).map_err(failure)?;
                if op.word() != [row.arrow().clone()]
                    || endpoint(&op.source())? != source
                    || endpoint(&op.target())? != target
                {
                    return Err("内部arrowの生成操作が元候補と違う".into());
                }
                let map = push(&mut parts, base, Part::Map { candidate }, c)?;
                operation = Some(push(
                    &mut parts,
                    base,
                    Part::Operation {
                        kernel: Box::new(op),
                        subject,
                        source,
                        target,
                        candidate,
                        map,
                        action,
                    },
                    c,
                )?);
            }
        } else if row.map().is_some() {
            return Err("内部arrowが候補なしで保存済みになった".into());
        }
        let mut evidence = vec![];
        for counterexample in row.counterexamples() {
            tick(c)?;
            let endpoint_component = |component: Option<&crate::construction::ObjectComponent>| -> Result<NodeRef, ValidationFailure> {
                let component = component.ok_or("内部arrow反例の元端点が未確定")?;
                let index = a.readings().objects().iter()
                    .position(|o| o.identity().subject() == component.subject())
                    .ok_or("内部arrow反例の端点が元対象表にない")?;
                objects.architectures.get(index).copied()
                    .ok_or_else(|| "内部arrow反例の実Architectureがない".into())
            };
            let left = endpoint_component(row.source())?;
            let right = endpoint_component(row.target())?;
            evidence.push(push(
                &mut parts,
                base,
                Part::Evidence {
                    subject,
                    left,
                    right,
                    facts: native::counterexample_facts(counterexample),
                },
                c,
            )?);
        }
        rows.push(Row {
            subject,
            candidate: candidate_ref,
            evidence,
            missing: row.missing().to_vec(),
            operation,
        });
    }
    tick(c)?;
    Ok((
        parts,
        Diagram {
            rows,
            all_preserved: core.all_preserved(),
        },
    ))
}
fn metadata(
    graph: &Graph,
    reference: NodeRef,
    universe: NodeRef,
) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
    let architecture = graph.get(reference)?;
    let universe = graph.get(universe)?;
    let mut support = architecture.support.clone();
    support.extend_from_slice(&universe.support);
    support.sort_by_key(|f| f.wire().canonical());
    support.dedup();
    let mut scope = architecture.scope.clone();
    scope.merge(&universe.scope);
    Ok((support, scope))
}
impl Source {
    fn recheck(
        &self,
        graph: &Graph,
        inputs: &CheckedInputs,
        a: &Arc<ArchitectureWitness>,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        tick(c)?;
        let (original, objects) =
            original(graph, self.reference, self.objects.base, self.universe)?;
        if inputs.sources() != self.inputs.sources()
            || inputs.sources() != Witness::Architecture(a.clone()).inputs().sources()
            || !Arc::ptr_eq(a, original)
            || !Arc::ptr_eq(a, &self.architecture)
            || objects != self.objects
        {
            return Err("内部arrowの元三入力・consumer・対象表が違う".into());
        }
        self.core.recheck(inputs, c).map_err(failure)?;
        let (parts, outputs) = plan(inputs, a, &objects, self.universe, self.base, &self.core, c)?;
        let (support, scope) = metadata(graph, self.reference, self.universe)?;
        if parts != self.parts
            || outputs != self.outputs
            || support != self.support
            || scope != self.scope
        {
            return Err("内部arrowの全計画・元検査・支持・scopeが違う".into());
        }
        tick(c)
    }
}
/// 未完成の対象族は呼出し側で保持し、この接続へ渡さない。
pub(super) fn retain(
    graph: &mut Graph,
    inputs: Arc<CheckedInputs>,
    reference: NodeRef,
    objects: &Objects,
    universe: NodeRef,
    c: &mut Control,
) -> Result<Diagram, ValidationFailure> {
    tick(c)?;
    if graph.active != graph.context_at(reference.0) {
        return Err("内部arrowの生成が元Requestでない".into());
    }
    let (a, current) = original(graph, reference, objects.base, universe)?;
    if &current != objects
        || inputs.sources() != Witness::Architecture(a.clone()).inputs().sources()
    {
        return Err("内部arrowの入力または対象表が違う".into());
    }
    let core = internal_arrows(
        &inputs,
        a.construction().reading(),
        &a.construction().root().snapshot,
        &a.construction().root().subject,
        c,
    )
    .map_err(|e| failure(e.cause().clone()))?;
    let (parts, outputs) = plan(&inputs, a, objects, universe, graph.nodes.len(), &core, c)?;
    let (support, scope) = metadata(graph, reference, universe)?;
    let source = Arc::new(Source {
        inputs,
        architecture: a.clone(),
        reference,
        objects: objects.clone(),
        universe,
        base: graph.nodes.len(),
        core,
        parts,
        outputs,
        support,
        scope,
    });
    source.recheck(graph, &source.inputs, &source.architecture, c)?;
    for index in 0..source.parts.len() {
        tick(c)?;
        let data = Data {
            source: source.clone(),
            index,
        };
        data.position(graph.nodes.len())?;
        native::retain(
            graph,
            ConstructionValue {
                witness: Witness::Architecture(source.architecture.clone()),
                data: D::InternalArrows(data),
            },
            vec![],
            vec![],
            None,
        )?;
    }
    tick(c)?;
    Ok(source.outputs.clone())
}
pub(super) fn validate_node(
    graph: &Graph,
    node: &Node,
    data: &Data,
) -> Result<(), ValidationFailure> {
    let part = data
        .source
        .parts
        .get(data.index)
        .ok_or("内部arrowの元計画添字がない")?;
    let Some(Payload::Construction(v)) = &node.payload else {
        return Err("内部arrowのpayloadがない".into());
    };
    let Witness::Architecture(a) = &v.witness else {
        return Err("内部arrowのconsumerがArchitectureでない".into());
    };
    let (current, objects) = original(
        graph,
        data.source.reference,
        data.source.objects.base,
        data.source.universe,
    )?;
    let (support, scope) = data.metadata();
    if !Arc::ptr_eq(a, current)
        || !Arc::ptr_eq(a, &data.source.architecture)
        || objects != data.source.objects
        || node.ty != part.ty()
        || node.rule != Rule::Construction(part.construction())
        || node.arguments != data.arguments()
        || node.support != support
        || node.scope != scope
        || !node.reasons.is_empty()
        || !node.evidence.is_empty()
        || node.judgment.is_some()
    {
        return Err("内部arrowの型・辺・元由来・支持・scopeが違う".into());
    }
    for r in part.arguments() {
        if r == data.source.reference
            || r == data.source.universe
            || data.source.objects.architectures.contains(&r)
        {
            graph.get(r)?;
            continue;
        }
        let Some(Payload::Construction(v)) = &graph.get(r)?.payload else {
            return Err("内部arrowの引数がnativeでない".into());
        };
        let D::InternalArrows(other) = &v.data else {
            return Err("内部arrowの引数が別由来".into());
        };
        if !Arc::ptr_eq(&other.source, &data.source)
            || other.index >= data.index
            || data.source.base.checked_add(other.index) != Some(r.0)
        {
            return Err("内部arrowの引数が元計画の既出値でない".into());
        }
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_internal_arrows(
        &self,
        graph: &Graph,
        value: &ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        let D::InternalArrows(data) = &value.data else {
            return Ok(());
        };
        let Witness::Architecture(a) = &value.witness else {
            return Err("内部arrowのconsumerがArchitectureでない".into());
        };
        let (current, objects) = original(
            graph,
            data.source.reference,
            data.source.objects.base,
            data.source.universe,
        )?;
        if !Arc::ptr_eq(a, current)
            || !Arc::ptr_eq(a, &data.source.architecture)
            || objects != data.source.objects
        {
            return Err("内部arrowのconsumerが元対象族と違う".into());
        }
        if self
            .verified_internal_arrows
            .borrow()
            .iter()
            .any(|s| Arc::ptr_eq(s, &data.source))
        {
            return Ok(());
        }
        data.source
            .recheck(graph, self.inputs, a, &mut self.control.clone())?;
        self.verified_internal_arrows
            .borrow_mut()
            .push(data.source.clone());
        Ok(())
    }
}
#[cfg(test)]
#[path = "internal_arrow_diagram_tests.rs"]
mod tests;
