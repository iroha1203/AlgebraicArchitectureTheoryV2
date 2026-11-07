//! 検査済みの局所対応を、既出ModelAssemblyの対象・操作・Lawへ接続する。
use super::{
    PreparedObserved, assembly_plan,
    build_plan::Plan,
    build_result::{Builder, Part},
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, Witness,
    },
    environment::{AnswerBinding, Environment, change_search},
    model_assembly::Model,
    model_map_assembly::{self as core, Failure},
    native_source::Boundary,
    projection::{MapAssemblyProjection, ProjectionStep, ProjectionType},
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::construction::{ConstructionFailure, maps::ConfigurationMap};
use archsig_common::{
    canonical::Json,
    control::{Checkpoint, Control},
    types::Type,
};
use std::{collections::BTreeMap, sync::Arc};
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ConfigurationMap)?;
    Ok(())
}
fn failure(e: ConstructionFailure) -> ValidationFailure {
    match e {
        ConstructionFailure::Stopped(s) => s.into(),
        e => e
            .internal_context(format!("全体写像の組立て: {e:?}"))
            .into(),
    }
}
fn fact(v: &Scalar) -> Result<Fact, ValidationFailure> {
    let Scalar::Subject {
        snapshot, subject, ..
    } = v
    else {
        return Err(internal!("correspondence集合の要素が参照でない").into());
    };
    Ok(Fact::from(archsig_input::archmap::FactData {
        snapshot: snapshot.clone(),
        subject: subject.clone(),
        field: None,
        atom: None,
    }))
}
fn plan(g: &Graph, r: NodeRef) -> Result<&Plan, ValidationFailure> {
    g.expect(r, &NodeType::Construction(T::ModelAssembly))?;
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err(internal!("ModelAssemblyがnativeでない").into());
    };
    let D::Build(d) = &v.data else {
        return Err(internal!("ModelAssemblyの元buildがない").into());
    };
    if d.answer().outputs.get("assembly") != Some(&r) {
        return Err(internal!("ModelAssemblyが元buildの出力でない").into());
    }
    Ok(d.plan())
}
fn model(p: &Plan) -> Result<Arc<Model>, ValidationFailure> {
    p.assembly
        .as_ref()
        .and_then(|a| a.model.clone())
        .ok_or_else(|| internal!("組立て済みのモデルがない").into())
}
#[cfg_attr(test, derive(Clone))]
struct Computed {
    parts: Vec<Part>,
    answer: Answer,
    maps: BTreeMap<usize, ConfigurationMap>,
    actions: BTreeMap<usize, ConfigurationMap>,
}
#[cfg_attr(test, derive(Clone))]
pub(super) struct Source {
    inputs: Arc<archsig_input::input::CheckedInputs>,
    request: Request,
    witness: Arc<ArchitectureWitness>,
    references: [NodeRef; 2],
    binding_refs: BTreeMap<String, NodeRef>,
    boundary: Boundary,
    base: usize,
    shape: MapAssemblyProjection,
    computed: Computed,
}
#[derive(Clone)]
pub(crate) struct Data {
    source: Arc<Source>,
    index: usize,
}
impl std::fmt::Debug for Data {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ModelMapAssemblyData")
            .field("base", &self.source.base)
            .field("index", &self.index)
            .finish()
    }
}
impl PartialEq for Data {
    fn eq(&self, o: &Self) -> bool {
        Arc::ptr_eq(&self.source, &o.source) && self.index == o.index
    }
}
impl Eq for Data {}
impl Data {
    fn part(&self) -> &Part {
        &self.source.computed.parts[self.index]
    }
    pub(super) fn evidence_kind(&self) -> Option<EvidenceKind> {
        self.part().evidence_kind()
    }
    pub(super) fn ty(&self) -> NodeType {
        self.part().ty.clone()
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        self.part().scalar.as_ref()
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part().construction
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        self.part().arguments.clone()
    }
    pub(super) fn conditions(&self) -> Vec<NodeRef> {
        self.part()
            .arguments
            .iter()
            .copied()
            .filter(|r| {
                r.0 >= self.source.base
                    && self
                        .source
                        .computed
                        .parts
                        .get(r.0 - self.source.base)
                        .is_some_and(|p| p.ty == NodeType::Proposition)
            })
            .collect()
    }
    pub(super) fn retained_metadata(&self) -> (Support, Scope) {
        (self.part().support.clone(), self.part().scope.clone())
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.part().support.to_vec(), self.part().scope.clone())
    }
    pub(super) fn wire(&self) -> Json {
        if let Some(map) = self.source.computed.actions.get(&self.index) {
            let mut wire = self.part().wire();
            if let Json::Obj(fields) = &mut wire {
                fields.insert(
                    "images".into(),
                    Json::Arr(map.candidate().images().iter().map(Fact::wire).collect()),
                );
            }
            wire
        } else {
            self.part().wire()
        }
    }
    pub(super) fn map_components(&self) -> Option<(NodeRef, NodeRef, NodeRef, Vec<NodeRef>)> {
        if self.ty() != NodeType::Construction(T::ConfigurationMap) {
            return None;
        }
        let candidate = self.part().reference("candidate")?;
        let row = self
            .source
            .computed
            .parts
            .get(candidate.0.checked_sub(self.source.base)?)?;
        Some((
            row.reference("source")?,
            row.reference("target")?,
            row.reference("action")?,
            vec![],
        ))
    }
    pub(super) fn action_universe(&self) -> Option<NodeRef> {
        (self.ty() == NodeType::Construction(T::AtomMap))
            .then(|| self.part().reference("universe"))
            .flatten()
    }
    pub(super) fn core_map(&self) -> Option<&ConfigurationMap> {
        self.source.computed.maps.get(&self.index)
    }
    pub(super) fn projection_type(&self) -> Option<ProjectionType> {
        let shape = || super::projection::MapProjection {
            declaration: String::new(),
            source: self.source.shape.source.root.clone(),
            target: self.source.shape.target.root.clone(),
        };
        match self.ty() {
            NodeType::Construction(T::ModelMapAssembly) => {
                Some(ProjectionType::ModelMapAssembly(self.source.shape.clone()))
            }
            NodeType::Construction(T::ConfigurationMap) => {
                Some(ProjectionType::ConfigurationMap(shape()))
            }
            NodeType::Construction(T::MapCandidate) => Some(ProjectionType::MapCandidate(shape())),
            NodeType::Construction(T::AtomMap) => Some(ProjectionType::AtomMap),
            _ => None,
        }
    }
    pub(super) fn project(&self, path: &[ProjectionStep]) -> Option<(NodeRef, usize)> {
        self.projection_type()?;
        self.part().project(path)
    }
    pub(super) fn validate_origin(&self, r: &Request) -> Result<(), ValidationFailure> {
        if r != &self.source.request || r.kind != QuestionKind::AssembleMap {
            return Err(internal!("全体写像の元Requestが違う").into());
        }
        Ok(())
    }
    fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        if self.index >= self.source.computed.parts.len()
            || at != self.source.base + self.index
            || self.arguments().iter().any(|r| r.0 >= at)
        {
            return Err(internal!("全体写像の位置・既出辺が違う").into());
        }
        Ok(())
    }
}
fn put_map(
    b: &mut Builder<'_>,
    map: &ConfigurationMap,
    source: NodeRef,
    target: NodeRef,
    universe: NodeRef,
    proof: NodeRef,
    maps: &mut BTreeMap<usize, ConfigurationMap>,
    actions: &mut BTreeMap<usize, ConfigurationMap>,
) -> Result<(NodeRef, NodeRef), ValidationFailure> {
    let action = b.push(
        NodeType::Construction(T::AtomMap),
        "atom_map",
        Json::obj([("universe", universe.wire())]),
        vec![universe, proof],
        None,
    )?;
    actions.insert(action.0 - b.base, map.clone());
    let candidate = b.push(
        NodeType::Construction(T::MapCandidate),
        "map_candidate",
        Json::obj([
            ("source", source.wire()),
            ("target", target.wire()),
            ("action", action.wire()),
        ]),
        vec![source, target, action, proof],
        None,
    )?;
    maps.insert(candidate.0 - b.base, map.clone());
    let reference = b.push(
        NodeType::Construction(T::ConfigurationMap),
        "configuration_map",
        Json::obj([("candidate", candidate.wire())]),
        vec![candidate, proof],
        None,
    )?;
    maps.insert(reference.0 - b.base, map.clone());
    Ok((candidate, reference))
}
struct LawNodes {
    source: [NodeRef; 3],
    target: Option<[NodeRef; 3]>,
}
fn law_nodes(
    law: &super::object_law_transport::ObjectLawTransport,
    source: &Plan,
    target: &Plan,
) -> Result<LawNodes, ValidationFailure> {
    let side = |plan: &Plan,
                readings: &crate::construction::readings::ObjectReadingInstances,
                object: &crate::construction::maps::ObjectIdentity,
                instance: &crate::construction::readings::ObjectInstance|
     -> Result<[NodeRef; 3], ValidationFailure> {
        let object = readings
            .objects()
            .iter()
            .position(|o| o.identity() == object)
            .ok_or(internal!("Law移送の実対象が元表にない"))?;
        let instance = readings
            .instances()
            .iter()
            .position(|i| i == instance)
            .ok_or(internal!("Law移送の実束縛が元表にない"))?;
        let rank = readings.instances()[..instance]
            .iter()
            .filter(|i| i.declaration().kind == "law")
            .count();
        let row = plan
            .laws
            .as_ref()
            .and_then(|t| t.objects.get(object))
            .ok_or(internal!("Law移送の実対象行がない"))?;
        Ok([
            row.object,
            *row.origins
                .get(rank)
                .ok_or(internal!("Law移送の元Law参照がない"))?,
            *row.evaluations
                .get(rank)
                .ok_or(internal!("Law移送の元評価がない"))?,
        ])
    };
    let source = side(source, law.source_readings(), law.object(), law.instance())?;
    let target = match (law.target_object(), law.target_instance()) {
        (Some(object), Some(instance)) => {
            Some(side(target, law.target_readings(), object, instance)?)
        }
        _ => None,
    };
    Ok(LawNodes { source, target })
}
fn compute(
    e: &Environment<'_>,
    g: &Graph,
    inputs: Arc<archsig_input::input::CheckedInputs>,
    r: &Request,
    refs: [NodeRef; 2],
    binding_refs: &BTreeMap<String, NodeRef>,
    base: usize,
    c: &Control,
) -> Result<Computed, ValidationFailure> {
    tick(c)?;
    let source_plan = plan(g, refs[0])?;
    let target_plan = plan(g, refs[1])?;
    let source = model(source_plan)?;
    let target = model(target_plan)?;
    let mut values = Vec::new();
    for a in &r.arguments {
        if let Some(name) = a.name.strip_prefix("bind.") {
            tick(c)?;
            values.push((name.to_owned(), change_search::selector(e, g, &a.value)?));
        }
    }
    let head = r.declaration().ok_or(internal!("対応Viewがない"))?;
    let read = assembly_plan::read(e, head, &values)?;
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let mut bindings = Vec::new();
    for (name, value) in &values {
        let at = if let Some(&reference) = binding_refs.get(name) {
            reference
        } else {
            let at = b.scalar(
                NodeType::Value(value.ty()),
                "binding",
                value.clone(),
                vec![],
            )?;
            if let Scalar::Subject {
                snapshot, subject, ..
            } = value
            {
                let holder = e.indexes.subject(snapshot, subject)?;
                let part = &mut b.parts[at.0 - base];
                part.support
                    .make_owned()
                    .push(Fact::from(archsig_input::archmap::FactData {
                        snapshot: snapshot.clone(),
                        subject: subject.clone(),
                        field: None,
                        atom: None,
                    }));
                part.support.make_owned().sort();
                part.support.make_owned().dedup();
                part.scope.merge(
                    &e.indexes
                        .scope(holder, source.construction.reading(), None)?,
                );
            }
            at
        };
        bindings.push(Binding {
            name: name.clone(),
            ty: value.ty(),
            value: at,
        });
    }
    let archsig_input::law::model::Signature::View { returns, body, .. } =
        &inputs.law().declarations()[head].signature
    else {
        return Err(internal!("対応集合の元がViewでない").into());
    };
    let expression = b.push(
        NodeType::Expression(returns.erase()),
        "expression",
        Json::obj([
            ("kind", Json::str("source")),
            (
                "location",
                archsig_input::result::location_wire(&archsig_common::issue::Location::Law {
                    span: inputs.law().exprs()[*body].span,
                }),
            ),
            ("parameters", Json::Arr(vec![])),
            (
                "bindings",
                Json::Arr(
                    bindings
                        .iter()
                        .map(|v| {
                            Json::obj([("name", Json::str(&v.name)), ("value", v.value.wire())])
                        })
                        .collect(),
                ),
            ),
        ]),
        bindings.iter().map(|v| v.value).collect(),
        None,
    )?;
    let part = &mut b.parts[expression.0 - base];
    if !read.metadata.support.is_empty() {
        part.support
            .make_owned()
            .extend(read.metadata.support.iter().cloned());
        part.support.make_owned().sort();
        part.support.make_owned().dedup();
    }
    part.scope.merge(&read.metadata.scope);
    let value = if let Some(value) = read.value {
        let mut existing = None;
        for &reference in binding_refs.values() {
            let original = g.scalar(reference)?;
            if original.ty() == value.ty() && super::data::equal(original, &value, c)? {
                existing = Some(reference);
                break;
            }
        }
        Some(match existing {
            Some(reference) => reference,
            None => b.scalar(
                NodeType::Value(value.ty()),
                "binding",
                value,
                vec![expression],
            )?,
        })
    } else {
        None
    };
    let mut failed = None;
    let mut verified = None;
    if !read.metadata.missing.is_empty() {
        failed = Some(Failure::Missing(read.metadata.missing.clone()));
    } else if read.metadata.failed {
        failed = Some(Failure::Coverage {
            facts: read.metadata.support.clone(),
        });
    } else if source.construction.root().snapshot != target.construction.root().snapshot
        || source.construction.reading() != target.construction.reading()
    {
        failed = Some(Failure::Unsupported {
            correspondence: source.construction.root().clone(),
            location: archsig_common::issue::Location::Law {
                span: inputs.law().exprs()[*body].span,
            },
        });
    } else if read.unsupported.is_none() && !read.metadata.blocked {
        let collection = match value {
            Some(at) if at.0 < base => Some(g.scalar(at)?),
            Some(at) => b.parts[at.0 - base].scalar.as_ref(),
            None => None,
        };
        let Some(Scalar::Set { items, .. }) = collection else {
            return Err(internal!("原始correspondenceの型付き集合がない").into());
        };
        let cs = items.iter().map(fact).collect::<Result<Vec<_>, _>>()?;
        match core::select(&inputs, &source, &target, &cs, c).map_err(failure)? {
            Err(f) => failed = Some(f),
            Ok(locals) => {
                match core::glue(&inputs, &source, &target, locals, c).map_err(failure)? {
                    Err(f) => failed = Some(f),
                    Ok(glued) => {
                        verified =
                            Some(
                                core::verify(
                                    Arc::clone(&inputs),
                                    &source,
                                    &target,
                                    glued,
                                    [
                                        source_plan.architecture.witness.shared_evaluations(),
                                        target_plan.architecture.witness.shared_evaluations(),
                                    ],
                                    c,
                                )
                                .map_err(|f| {
                                    c.stop_reason().map(ValidationFailure::Stop).unwrap_or_else(
                                        || f.internal_context("全体写像のLaw検査".into()).into(),
                                    )
                                })?,
                            );
                    }
                }
            }
        }
    }
    let label = b.scalar(
        NodeType::Value(Type::Text),
        "binding",
        Scalar::Text("model_map_assembly".into()),
        vec![refs[0], refs[1], expression],
    )?;
    let local_condition = b.proposition(
        "constructible",
        vec![label, expression],
        vec![refs[0], refs[1]],
        if verified.is_some() {
            Decision::Established
        } else {
            match &failed {
                Some(
                    Failure::Coverage { .. }
                    | Failure::SharedImage { .. }
                    | Failure::Preservation { .. }
                    | Failure::Square { .. },
                ) => Decision::Refuted,
                _ => Decision::Undetermined,
            }
        },
    )?;
    if let Some(verified) = &verified {
        let part = &mut b.parts[local_condition.0 - base];
        for local in &verified.glued.locals {
            let holder = e.indexes.subject(
                &local.correspondence.snapshot,
                &local.correspondence.subject,
            )?;
            part.support.make_owned().push(local.correspondence.clone());
            part.scope.merge(
                &e.indexes
                    .scope(holder, source.construction.reading(), None)?,
            );
            for field in &holder.fields {
                tick(c)?;
                if let archsig_input::archmap::Slot::Known { atom, origin, .. } = &field.slot {
                    let mut fact = super::model_assembly::field_fact(holder, field);
                    fact.atom = Some(atom.clone());
                    part.support.make_owned().push(fact);
                    part.scope.merge(&e.indexes.scope(
                        holder,
                        source.construction.reading(),
                        Some(origin),
                    )?);
                }
            }
        }
        part.support.make_owned().sort();
        part.support.make_owned().dedup();
    }
    let mut maps = BTreeMap::new();
    let mut actions = BTreeMap::new();
    let mut fields: BTreeMap<String, NodeRef> = BTreeMap::new();
    let mut local_fields = Vec::new();
    let mut outputs = BTreeMap::new();
    let mut evidence = Vec::new();
    let mut conditions = vec![local_condition];
    let mut reasons = Vec::new();
    let mut status = if let Some(v) = &verified {
        if v.all_preserved() {
            Decision::Established
        } else if v.transport.all_preserved()
            && (!v.unsupported_instances.is_empty()
                || v.laws.iter().any(|law| {
                    matches!(
                        law.outcome(),
                        super::object_law_transport::LawTransportOutcome::Undetermined
                    )
                }))
        {
            Decision::Undetermined
        } else {
            Decision::Refuted
        }
    } else {
        b.parts[local_condition.0 - base]
            .judgment
            .as_ref()
            .unwrap()
            .status
    };
    if let Some(v) = &verified {
        let (candidate, map) = put_map(
            &mut b,
            &v.glued.map,
            source_plan.architecture.reference,
            target_plan.architecture.reference,
            source_plan.architecture.universe,
            local_condition,
            &mut maps,
            &mut actions,
        )?;
        outputs.insert("candidate".into(), candidate);
        outputs.insert("configuration_map".into(), map);
        if v.all_preserved() {
            fields.extend([
                ("source".into(), source_plan.architecture.reference),
                ("target".into(), target_plan.architecture.reference),
                ("source_assembly".into(), refs[0]),
                ("target_assembly".into(), refs[1]),
                ("configuration_map".into(), map),
                (
                    "correspondences".into(),
                    value.ok_or(internal!("対応集合値がない"))?,
                ),
            ]);
            let mut locals = Vec::new();
            for (i, local) in v.glued.locals.iter().enumerate() {
                tick(c)?;
                let s = &source_plan.assembly.as_ref().unwrap().locals[local.source];
                let t = &target_plan.assembly.as_ref().unwrap().locals[local.target];
                let entity = e
                    .indexes
                    .subject(
                        &local.correspondence.snapshot,
                        &local.correspondence.subject,
                    )?
                    .ty
                    .to_string();
                let raw = b.scalar(
                    NodeType::Value(Type::Ref(entity.clone())),
                    "binding",
                    Scalar::Subject {
                        snapshot: local.correspondence.snapshot.clone(),
                        subject: local.correspondence.subject.clone(),
                        entity,
                    },
                    vec![value.unwrap()],
                )?;
                let (_, mu) = put_map(
                    &mut b,
                    &local.map,
                    s.architecture.reference,
                    t.architecture.reference,
                    source_plan.architecture.universe,
                    local_condition,
                    &mut maps,
                    &mut actions,
                )?;
                let sr = &source_plan.assembly.as_ref().unwrap().restrictions[local.source];
                let tr = &target_plan.assembly.as_ref().unwrap().restrictions[local.target];
                let (_, restriction) = put_map(
                    &mut b,
                    &v.glued.restrictions[i],
                    sr.reference,
                    tr.reference,
                    source_plan.architecture.universe,
                    local_condition,
                    &mut maps,
                    &mut actions,
                )?;
                let p = b.proposition(
                    "constructible",
                    vec![label, raw, mu, restriction],
                    vec![local_condition],
                    Decision::Established,
                )?;
                let row: BTreeMap<String, NodeRef> = BTreeMap::from([
                    ("correspondence".into(), raw),
                    ("source".into(), s.architecture.reference),
                    ("target".into(), t.architecture.reference),
                    ("map".into(), mu),
                    ("restriction".into(), restriction),
                    ("proposition".into(), p),
                ]);
                locals.push(Json::Obj(
                    row.iter().map(|(k, v)| (k.clone(), v.wire())).collect(),
                ));
                local_fields.push(row);
            }
            let source_ops = super::assembly_output::operations(
                g,
                source_plan
                    .arrows
                    .as_ref()
                    .ok_or(internal!("元操作族がない"))?,
            )?;
            let target_ops = super::assembly_output::operations(
                g,
                target_plan
                    .arrows
                    .as_ref()
                    .ok_or(internal!("先操作族がない"))?,
            )?;
            let mut generators = Vec::new();
            let mut laws = Vec::new();
            let mut args = fields.values().copied().collect::<Vec<_>>();
            for generator in v.transport.generators() {
                let s = *source_ops
                    .get(generator.source())
                    .ok_or(internal!("元生成操作がない"))?;
                let t = *target_ops
                    .get(generator.target())
                    .ok_or(internal!("先生成操作がない"))?;
                let p = b.proposition(
                    "constructible",
                    vec![label, s, t, map],
                    vec![local_condition],
                    Decision::Established,
                )?;
                generators.push(Json::obj([
                    ("source", s.wire()),
                    ("target", t.wire()),
                    ("proposition", p.wire()),
                ]));
                args.extend([s, t, p]);
            }
            for law in &v.laws {
                let nodes = law_nodes(law, source_plan, target_plan)?;
                let [so, sl, _] = nodes.source;
                let [to, tl, _] = nodes
                    .target
                    .ok_or(internal!("保存されたLawの像参照がない"))?;
                let p = b.proposition(
                    "constructible",
                    vec![label, so, to, sl, tl, map],
                    vec![local_condition],
                    Decision::Established,
                )?;
                laws.push(Json::obj([
                    ("source_object", so.wire()),
                    ("target_object", to.wire()),
                    ("source_law", sl.wire()),
                    ("target_law", tl.wire()),
                    ("proposition", p.wire()),
                ]));
                args.extend([so, to, sl, tl, p]);
            }
            for row in &local_fields {
                args.extend(row.values().copied());
            }
            let mut wire: archsig_common::canonical::JsonObject =
                fields.iter().map(|(k, v)| (k.clone(), v.wire())).collect();
            wire.insert("locals".into(), Json::Arr(locals));
            wire.insert("generators".into(), Json::Arr(generators));
            wire.insert("laws".into(), Json::Arr(laws));
            let result = b.push(
                NodeType::Construction(T::ModelMapAssembly),
                "model_map_assembly",
                Json::Obj(wire),
                args,
                None,
            )?;
            outputs.insert("map".into(), result);
        }
    }
    if read.unsupported.is_some() || read.metadata.blocked {
        status = Decision::Undetermined;
    }
    // 元slotの未知と、実対応・Lawの反例を区別して保持する。
    if let Some(f) = &failed {
        let facts = match f {
            Failure::Missing(fs)
            | Failure::Coverage { facts: fs }
            | Failure::Preservation { facts: fs } => fs.clone(),
            Failure::Unsupported { correspondence, .. } => vec![correspondence.clone()],
            Failure::SharedImage {
                source,
                left,
                right,
                left_correspondence,
                right_correspondence,
            } => vec![
                source.clone(),
                left.clone(),
                right.clone(),
                left_correspondence.clone(),
                right_correspondence.clone(),
            ],
            Failure::Square {
                correspondence,
                difference,
                ..
            } => vec![
                correspondence.clone(),
                difference.fact().clone(),
                difference.left().clone(),
                difference.right().clone(),
            ],
        };
        if matches!(f, Failure::Missing(_)) {
            reasons.push(Reason {
                kind: ReasonKind::Missing,
                request: r.id.clone(),
                dependencies: vec![expression],
                missing: facts,
                location: None,
            });
        }
    }
    if let Some(v) = &verified {
        for &index in &v.unsupported_instances {
            let instance = &source_plan.architecture.witness.readings().instances()[index];
            reasons.push(Reason {
                kind: ReasonKind::UnsupportedAlgorithm {
                    question: r.kind,
                    operand_types: instance.parameters().iter().map(|p| p.ty.clone()).collect(),
                    method: "finite_model_map_law_family".into(),
                },
                request: r.id.clone(),
                dependencies: vec![expression],
                missing: vec![],
                location: Some(archsig_common::issue::Location::Law {
                    span: instance.declaration().span,
                }),
            });
        }
    }
    if let Some(Failure::Unsupported {
        correspondence,
        location,
    }) = &failed
    {
        reasons.push(Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: r.kind,
                operand_types: vec![Type::Ref(
                    e.indexes
                        .subject(&correspondence.snapshot, &correspondence.subject)?
                        .ty
                        .to_string(),
                )],
                method: "finite_model_map_construction".into(),
            },
            request: r.id.clone(),
            dependencies: vec![expression],
            missing: vec![],
            location: Some(location.clone()),
        });
    }
    if let Some(unsupported) = &read.unsupported {
        reasons.push(Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: r.kind,
                operand_types: vec![returns.clone()],
                method: unsupported.detail.clone(),
            },
            request: r.id.clone(),
            dependencies: vec![expression],
            missing: vec![],
            location: Some(unsupported.location.clone()),
        });
    }
    if status == Decision::Refuted {
        let mut facts = Vec::new();
        let mut action_difference = None;
        let mut overlap = None;
        let difference = |kind: &str, subject: &Fact, fact: &Fact, left: &Fact, right: &Fact| {
            Json::obj([
                ("kind", Json::str(kind)),
                ("subject", subject.wire()),
                ("fact", fact.wire()),
                ("left", left.wire()),
                ("right", right.wire()),
            ])
        };
        if let Some(Failure::Square {
            kind,
            correspondence,
            difference: d,
        }) = &failed
        {
            action_difference = Some(difference(
                kind.name(),
                correspondence,
                d.fact(),
                d.left(),
                d.right(),
            ));
        }
        if let Some(Failure::SharedImage {
            source,
            left,
            right,
            left_correspondence,
            right_correspondence,
        }) = &failed
        {
            overlap = Some(Json::obj([
                ("source", source.wire()),
                ("left_correspondence", left_correspondence.wire()),
                ("right_correspondence", right_correspondence.wire()),
                ("left", left.wire()),
                ("right", right.wire()),
            ]));
        }

        if let Some(f) = &failed {
            match f {
                Failure::Coverage { facts: fs } | Failure::Preservation { facts: fs } => {
                    facts.extend(fs.iter().cloned())
                }
                Failure::SharedImage {
                    source,
                    left,
                    right,
                    left_correspondence,
                    right_correspondence,
                } => facts.extend([
                    source.clone(),
                    left.clone(),
                    right.clone(),
                    left_correspondence.clone(),
                    right_correspondence.clone(),
                ]),
                Failure::Square {
                    correspondence,
                    difference,
                    ..
                } => facts.extend([
                    correspondence.clone(),
                    difference.fact().clone(),
                    difference.left().clone(),
                    difference.right().clone(),
                ]),
                _ => {}
            }
        }
        if let Some(v) = &verified {
            for local in &v.glued.locals {
                facts.push(local.correspondence.clone());
            }
        }
        facts.sort();
        facts.dedup();
        let mut left = value.unwrap_or(expression);
        let mut right = refs[1];
        let mut counter_bindings = bindings.clone();
        let mut counter_args = vec![local_condition];
        if let Some(v) = &verified {
            use super::object_law_transport::{LawConditionFailure as F, LawTransportOutcome as O};
            if let Some(law) = v
                .laws
                .iter()
                .find(|law| matches!(law.outcome(), O::Refuted(_)))
            {
                let nodes = law_nodes(law, source_plan, target_plan)?;
                counter_args.extend(nodes.source);
                facts.extend(g.get(nodes.source[2])?.support.iter().cloned());
                left = nodes.source[2];
                if let Some(target) = nodes.target {
                    right = target[2];
                    counter_args.extend(target);
                    facts.extend(g.get(target[2])?.support.iter().cloned());
                }
                let family = law.family().and_then(|family| {
                    family
                        .rows()
                        .iter()
                        .find(|row| matches!(row.outcome(), O::Refuted(_)))
                });
                let readings = if let Some(row) = family {
                    Some((row.source(), row.target(), row.outcome()))
                } else {
                    law.source_reading()
                        .zip(law.target_reading())
                        .map(|(a, b)| (a, b, law.outcome()))
                };
                if let Some((a, z, outcome)) = readings {
                    let (a, z) = match outcome {
                        O::Refuted(F::RequiredStatus { .. }) => {
                            (Some(a.required()), Some(z.required()))
                        }
                        O::Refuted(F::Applicability) => {
                            (a.application().value(), z.application().value())
                        }
                        O::Refuted(F::Holds) => (a.body(), z.body()),
                        _ => (None, None),
                    };
                    if let (Some(a), Some(z)) = (a, z) {
                        left = b.scalar(
                            NodeType::Value(Type::Bool),
                            "binding",
                            Scalar::Bool(a),
                            counter_args.clone(),
                        )?;
                        right = b.scalar(
                            NodeType::Value(Type::Bool),
                            "binding",
                            Scalar::Bool(z),
                            counter_args.clone(),
                        )?;
                    }
                }
                counter_bindings.clear();
                for binding in law.instance().bindings() {
                    let raw = binding.subject();
                    let entity = e
                        .indexes
                        .subject(&raw.snapshot, &raw.subject)?
                        .ty
                        .to_string();
                    let scalar = Scalar::Subject {
                        snapshot: raw.snapshot.clone(),
                        subject: raw.subject.clone(),
                        entity,
                    };
                    let value = b.scalar(
                        NodeType::Value(scalar.ty()),
                        "binding",
                        scalar,
                        counter_args.clone(),
                    )?;
                    counter_bindings.push(Binding {
                        name: binding.parameter().name.clone(),
                        ty: binding.parameter().ty.erase(),
                        value,
                    });
                }
                if let Some(row) = family {
                    for (name, value) in row.source_bindings() {
                        let scalar = value.scalar();
                        let reference = b.scalar(
                            NodeType::Value(scalar.ty()),
                            "binding",
                            scalar.clone(),
                            counter_args.clone(),
                        )?;
                        counter_bindings.push(Binding {
                            name: name.clone(),
                            ty: scalar.ty(),
                            value: reference,
                        });
                    }
                }
            }
            for generator in v.transport.generators() {
                if let Some(crate::construction::maps::Naturality::Refuted { fact, left, right }) =
                    generator.naturality()
                {
                    facts.extend([fact.clone(), left.clone(), right.clone()]);
                    action_difference = Some(difference(
                        "generator",
                        generator.source(),
                        fact,
                        left,
                        right,
                    ));
                    break;
                }
            }
        }
        facts.sort();
        facts.dedup();
        counter_args.extend([left, right]);
        counter_args.extend(counter_bindings.iter().map(|b| b.value));
        let mut details: archsig_common::canonical::JsonObject = [
            (
                "bindings".into(),
                Json::Arr(
                    counter_bindings
                        .iter()
                        .map(|v| {
                            Json::obj([("name", Json::str(&v.name)), ("value", v.value.wire())])
                        })
                        .collect(),
                ),
            ),
            ("paths".into(), Json::Arr(vec![])),
            ("left".into(), left.wire()),
            ("right".into(), right.wire()),
            (
                "facts".into(),
                Json::Arr(facts.iter().map(Fact::wire).collect()),
            ),
        ]
        .into_iter()
        .collect();
        if let Some(value) = action_difference {
            details.insert("action_difference".into(), value);
        }
        if let Some(value) = overlap {
            details.insert("overlap".into(), value);
        }
        let counterexample = b.push(
            NodeType::Evidence,
            "evidence",
            Json::obj([
                ("kind", Json::str("counterexample")),
                ("data", Json::Obj(details)),
            ]),
            counter_args,
            None,
        )?;
        evidence.push(counterexample);
        let condition = b.proposition(
            "constructible",
            vec![label],
            vec![local_condition, counterexample],
            Decision::Refuted,
        )?;
        conditions.push(condition);
        reasons.push(Reason {
            kind: ReasonKind::ConditionFailed {
                condition,
                construction: "model_map_assembly",
            },
            request: r.id.clone(),
            dependencies: vec![condition],
            missing: vec![],
            location: None,
        });
    }
    sort_reasons(&mut reasons);
    let claim = b.proposition(
        "constructible",
        vec![label],
        outputs.values().copied().chain(conditions).collect(),
        status,
    )?;
    let part = &mut b.parts[claim.0 - base];
    part.reasons.extend(reasons.iter().cloned());
    sort_reasons(&mut part.reasons);
    part.evidence = evidence.clone();
    if let Some(judgment) = &mut part.judgment {
        judgment.reasons = part.reasons.clone();
        judgment.evidence = evidence.clone();
    }
    part.arguments.extend(evidence.iter().copied());
    outputs.insert("proposition".into(), claim);
    let scope = b.parts[claim.0 - base].scope.clone();
    Ok(Computed {
        parts: b.parts,
        answer: Answer {
            id: r.id.clone(),
            status,
            outputs,
            claim: Some(claim),
            evidence,
            reasons,
            scope,
        },
        maps,
        actions,
    })
}

pub(super) fn evaluate(
    p: &PreparedObserved,
    e: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
) -> Result<Answer, ValidationFailure> {
    <Data as super::result_kind::ResultKind>::compute_and_retain((p, e, g, r, c))
}
impl super::result_kind::ResultKind for Data {
    type Stored = Arc<Source>;
    type Input<'a, 'input: 'a> = (
        &'a PreparedObserved,
        &'a Environment<'input>,
        &'a mut Graph,
        &'a Request,
        &'a Control,
    );
    type Output = Answer;
    fn compute_and_retain<'a, 'input: 'a>(
        input: Self::Input<'a, 'input>,
    ) -> Result<Answer, ValidationFailure> {
        let (p, e, g, r, c) = input;
        if let Some(answer) = e.unavailable_binding_answer(g, r)? {
            return Ok(answer);
        }
        let mut selected = Vec::new();
        let mut dependencies = Vec::new();
        let mut binding_refs = BTreeMap::new();
        for key in ["from", "to"] {
            let selector = &r
                .arguments
                .iter()
                .find(|a| a.name == key)
                .ok_or(internal!("写像組立てのModelAssembly Handleがない"))?
                .value;
            let at = assembly_plan::reference(e, g, selector)?
                .ok_or(internal!("ModelAssemblyの既出参照がない"))?;
            plan(g, at)?;
            selected.push(at);
            dependencies.push(at);
        }
        for a in &r.arguments {
            if let Some(name) = a.name.strip_prefix("bind.")
                && let Some(at) = assembly_plan::reference(e, g, &a.value)?
            {
                dependencies.push(at);
                binding_refs.insert(name.to_owned(), at);
            }
        }
        let references = [selected[0], selected[1]];
        let witness = Arc::clone(&plan(g, references[0])?.architecture.witness);
        dependencies.sort_by_key(|r| r.0);
        dependencies.dedup();
        let boundary = Boundary::capture_existing(
            e,
            g,
            plan(g, references[0])?.architecture.reference,
            dependencies,
            c,
        )?;
        let base = g.nodes.len();
        let names = p
            .requests()
            .requests()
            .iter()
            .enumerate()
            .map(|(i, r)| (r.id.clone(), i))
            .collect();
        let shape = super::request::assembly_map::shape(
            p.inputs().law(),
            p.inputs().archmap(),
            p.requests().requests(),
            &names,
            r,
            c,
        )
        .map_err(|_| internal!("解決済み全体写像の署名が違う"))?;
        let computed = e.validation_graph_session(g, || {
            compute(
                e,
                g,
                p.shared_inputs(),
                r,
                references,
                &binding_refs,
                base,
                c,
            )
        })?;
        let source = Arc::new(Source {
            inputs: p.shared_inputs(),
            request: r.clone(),
            witness,
            references,
            binding_refs,
            boundary,
            base,
            shape,
            computed,
        });
        for index in 0..source.computed.parts.len() {
            tick(c)?;
            let part = &source.computed.parts[index];
            native::retain(
                g,
                ConstructionValue {
                    witness: Witness::Architecture(Arc::clone(&source.witness)),
                    data: D::ModelMap(Data {
                        source: Arc::clone(&source),
                        index,
                    }),
                },
                part.reasons.clone(),
                part.evidence.clone(),
                part.judgment.clone(),
            )?;
        }
        Ok(source.computed.answer.clone())
    }
    fn validate(
        &self,
        g: &Graph,
        n: &Node,
        v: &ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        let Witness::Architecture(w) = &v.witness else {
            return Err(internal!("全体写像の元Architectureがない").into());
        };
        let p = self.part();
        if !Arc::ptr_eq(w, &self.source.witness)
            || n.ty != p.ty
            || n.rule != Rule::Construction(p.construction)
            || n.arguments != p.arguments
            || n.support != p.support
            || n.scope != p.scope
            || n.reasons != p.reasons
            || n.judgment != p.judgment
            || n.evidence != p.evidence
        {
            return Err(internal!("全体写像のnative構成・辺・判断が違う").into());
        }
        for at in &p.arguments {
            g.get(*at)?;
        }
        Ok(())
    }
    fn recheck(
        &self,
        e: &Environment<'_>,
        g: &Graph,
        _v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        self.position(at)?;
        let c = e.control.clone();
        self.source.boundary.recheck(e, g, at, &c)?;
        let r = g
            .requests
            .get(self.source.boundary.producer_request())
            .ok_or(internal!("全体写像の元producerがない"))?;
        self.validate_origin(r)?;
        if e.results.source_checked(&self.source) {
            return Ok(());
        }
        let names = g
            .requests
            .iter()
            .enumerate()
            .map(|(i, r)| (r.id.clone(), i))
            .collect();
        let shape = super::request::assembly_map::shape(
            e.indexes.inputs.law(),
            e.indexes.inputs.archmap(),
            &g.requests,
            &names,
            r,
            &c,
        )
        .map_err(|_| {
            c.stop_reason()
                .map(ValidationFailure::Stop)
                .unwrap_or_else(|| internal!("全体写像の現在署名を解決できない").into())
        })?;
        if shape != self.source.shape {
            return Err(internal!("全体写像の公開署名が元View・ModelAssemblyと違う").into());
        }
        for (key, expected) in ["from", "to"].into_iter().zip(self.source.references) {
            let selector = &r
                .arguments
                .iter()
                .find(|a| a.name == key)
                .ok_or(internal!("組立ての元Handleがない"))?
                .value;
            if !matches!(e.answer_binding(g,selector,(0,0))?,AnswerBinding::Reference(actual) if actual==expected)
            {
                return Err(internal!("全体写像が要求されたModelAssemblyを使っていない").into());
            }
        }
        let mut expected_bindings = 0;
        for a in &r.arguments {
            let Some(name) = a.name.strip_prefix("bind.") else {
                continue;
            };
            if matches!(&a.value, Selector::Answer { .. }) {
                expected_bindings += 1;
                let saved = *self
                    .source
                    .binding_refs
                    .get(name)
                    .ok_or(internal!("写像組立ての元束縛辺がない"))?;
                match e.answer_binding(g, &a.value, (0, 0))? {
                    AnswerBinding::Reference(actual) if actual == saved => {}
                    AnswerBinding::Projection(node) if g.get(saved)? == &node => {}
                    _ => return Err(internal!("写像組立ての束縛が元Handleと違う").into()),
                }
            } else if self.source.binding_refs.contains_key(name) {
                return Err(internal!("原始束縛へ架空のHandle辺を付けた").into());
            }
        }
        if expected_bindings != self.source.binding_refs.len() {
            return Err(internal!("写像組立ての束縛辺の数が違う").into());
        }
        let inputs = Arc::clone(&self.source.inputs);
        if inputs.sources() != e.indexes.inputs.sources() {
            return Err(internal!("全体写像の元三入力が現在入力と違う").into());
        }
        let expected = e.validation_graph_session(g, || {
            compute(
                e,
                g,
                inputs,
                r,
                self.source.references,
                &self.source.binding_refs,
                self.source.base,
                &c,
            )
        })?;
        if expected.parts != self.source.computed.parts
            || expected.answer != self.source.computed.answer
            || expected.maps != self.source.computed.maps
            || expected.actions != self.source.computed.actions
        {
            return Err(internal!("全体写像の再構成が元対応・作用・Lawと違う").into());
        }
        e.results.remember(Arc::clone(&self.source));
        Ok(())
    }
}

pub(super) fn validate_answer(
    e: &Environment<'_>,
    g: &Graph,
    r: &Request,
    a: &Answer,
) -> Result<(), ValidationFailure> {
    if let Some(expected) = e.unavailable_binding_answer(g, r)? {
        return if a == &expected {
            Ok(())
        } else {
            Err(internal!("全体写像の依存停止回答が元導出と違う").into())
        };
    }
    let at = a.claim.ok_or(internal!("全体写像の構成命題がない"))?;
    let Some(Payload::Construction(v)) = &g.get(at)?.payload else {
        return Err(internal!("全体写像の命題がnativeでない").into());
    };
    let D::ModelMap(data) = &v.data else {
        return Err(internal!("全体写像の命題が別構成").into());
    };
    data.validate_origin(r)?;
    <Data as super::result_kind::ResultKind>::recheck(data, e, g, v, at.0)?;
    if a != &data.source.computed.answer {
        return Err(internal!("全体写像の回答が再検査結果と違う").into());
    }
    Ok(())
}

#[cfg(test)]
mod tests;
