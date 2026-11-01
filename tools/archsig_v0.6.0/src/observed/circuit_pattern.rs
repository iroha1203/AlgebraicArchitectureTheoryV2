//! 既存の完全query patternを、元標準対象と同じUのnative DAGへ保持する。
use super::{
    construction_result as native,
    construction_result::{
        ArchitectureWitness, ConstructionData as D, ConstructionType as T, ConstructionValue,
        Witness,
    },
    environment::Environment,
    object_component_diagram::Diagram as Objects,
    result::*,
};
use crate::{
    canonical::Json,
    construction::{
        ConstructionFailure,
        profiles::{CircuitQuery, ConfigurationProfiles, construct_profiles},
    },
};
use crate::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
};
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ConfigurationProfile)?;
    Ok(())
}
fn failure(e: ConstructionFailure) -> ValidationFailure {
    match e {
        ConstructionFailure::Stopped(s) => s.into(),
        e => format!("完全query patternの構成: {e:?}").into(),
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Query {
    Atom {
        atom: Fact,
        present: bool,
    },
    Relation {
        left: Fact,
        right: Fact,
        present: bool,
    },
    Identification {
        left: Fact,
        right: Fact,
        present: bool,
    },
}
impl Query {
    fn wire(&self) -> Json {
        match self {
            Self::Atom { atom, present } => Json::obj([
                ("kind", Json::str("atom")),
                ("atom", atom.wire()),
                ("present", Json::Bool(*present)),
            ]),
            Self::Relation {
                left,
                right,
                present,
            }
            | Self::Identification {
                left,
                right,
                present,
            } => Json::obj([
                (
                    "kind",
                    Json::str(if matches!(self, Self::Relation { .. }) {
                        "relation"
                    } else {
                        "identification"
                    }),
                ),
                ("left", left.wire()),
                ("right", right.wire()),
                ("present", Json::Bool(*present)),
            ]),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Output {
    universe: NodeRef,
    queries: Vec<Query>,
}
impl Output {
    fn wire(&self) -> Json {
        Json::obj([
            ("universe", self.universe.wire()),
            (
                "queries",
                Json::Arr(self.queries.iter().map(Query::wire).collect()),
            ),
        ])
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Row {
    pub object: NodeRef,
    pub pattern: NodeRef,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Diagram {
    pub architecture: NodeRef,
    pub universe: NodeRef,
    pub rows: Vec<Row>,
}
#[derive(Clone)]
pub(super) struct Source {
    inputs: Arc<CheckedInputs>,
    architecture: Arc<ArchitectureWitness>,
    reference: NodeRef,
    components: NodeRef,
    objects: Objects,
    universe: NodeRef,
    profiles: ConfigurationProfiles,
    base: usize,
    outputs: Vec<Output>,
    diagram: Diagram,
    support: Vec<Fact>,
    scope: Scope,
}
impl std::fmt::Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CircuitPatternSource")
            .field("reference", &self.reference)
            .field("base", &self.base)
            .finish()
    }
}
#[derive(Clone, Debug)]
pub(crate) struct Data {
    source: Arc<Source>,
    index: usize,
    output: Output,
}
impl PartialEq for Data {
    fn eq(&self, b: &Self) -> bool {
        Arc::ptr_eq(&self.source, &b.source) && self.index == b.index && self.output == b.output
    }
}
impl Eq for Data {}
fn original(
    env: &Environment<'_>,
    g: &Graph,
    inputs: &CheckedInputs,
    reference: NodeRef,
    components: Option<NodeRef>,
    c: &mut Control,
) -> Result<
    Option<(
        Arc<ArchitectureWitness>,
        NodeRef,
        Objects,
        NodeRef,
        Vec<Fact>,
        Scope,
    )>,
    ValidationFailure,
> {
    tick(c)?;
    if inputs.sources() != env.indexes.inputs.sources() {
        return Err("query patternの三入力が検査環境と違う".into());
    }
    let node = g.get(reference)?;
    env.recheck_node(g, node, reference.0)?;
    if node.ty != NodeType::Construction(T::Architecture) {
        return Err("query patternの元Architecture/Requestが違う".into());
    }
    let Some(Payload::Construction(value)) = &node.payload else {
        return Err("query patternのnative Architectureがない".into());
    };
    if matches!(
        value.data,
        D::Pending {
            ty: T::Architecture,
            ..
        }
    ) {
        return Ok(None);
    }
    let a = native::architecture_origin(g, reference, 0)?.clone();
    if inputs.sources() != Witness::Architecture(a.clone()).inputs().sources() {
        return Err("query patternの元入力がArchitectureと違う".into());
    }
    let Some(components) = components else {
        return Ok(None);
    };
    let node = g.get(components)?;
    env.recheck_node(g, node, components.0)?;
    let Some(Payload::Construction(v)) = &node.payload else {
        return Err("query patternの元対象表がnativeでない".into());
    };
    let D::ObjectComponents(data) = &v.data else {
        return Err("query patternの元対象表が別構成".into());
    };
    let (owner, base, objects) = data.retained_components();
    if !Arc::ptr_eq(&a, &owner)
        || base != reference
        || objects.base != components
        || objects.objects.len() != a.readings().objects().len()
        || objects.architectures.len() != objects.objects.len()
    {
        return Err("query patternの元全対象/Architecture/順序が違う".into());
    }
    let mut universe = None;
    for (i, n) in g.nodes.iter().enumerate().take(reference.0) {
        g.tick()?;
        if matches!(&n.payload,Some(Payload::Construction(v))if matches!(&v.data,D::AtomUniverse(atoms)if atoms==a.construction().universe()))
        {
            universe = Some(NodeRef(i));
            break;
        }
    }
    let universe = universe.ok_or("query patternの共通AtomUniverseがない")?;
    let mut support = vec![];
    let mut scope = Scope::default();
    for r in [reference, components, universe]
        .into_iter()
        .chain(objects.objects.iter().copied())
        .chain(objects.architectures.iter().copied())
    {
        tick(c)?;
        let n = g.get(r)?;
        env.recheck_node(g, n, r.0)?;
        support.extend(n.support.iter().cloned());
        scope.merge(&n.scope);
    }
    support.sort();
    support.dedup();
    tick(c)?;
    Ok(Some((a, components, objects, universe, support, scope)))
}
fn compute(
    inputs: &CheckedInputs,
    a: &ArchitectureWitness,
    objects: &Objects,
    universe: NodeRef,
    base: usize,
    c: &mut Control,
) -> Result<Option<(ConfigurationProfiles, Vec<Output>, Diagram)>, ValidationFailure> {
    tick(c)?;
    let root = a.construction().root();
    let profiles = construct_profiles(
        inputs,
        a.construction().reading(),
        &root.snapshot,
        &root.subject,
        c,
    )
    .map_err(failure)?;
    if profiles.construction() != a.construction() {
        return Err("query patternの構成が元Architectureと違う".into());
    }
    if !profiles.is_complete() {
        return Ok(None);
    }
    if profiles.profiles().len() != objects.objects.len() {
        return Err("query patternの全対象coverageが違う".into());
    }
    let mut outputs = vec![];
    let mut rows = vec![];
    for (index, (profile, object)) in profiles.profiles().iter().zip(&objects.objects).enumerate() {
        tick(c)?;
        if profile.object()
            != a.readings()
                .objects()
                .get(index)
                .ok_or("query patternの元対象番号が域外")?
                .identity()
        {
            return Err("query patternの対象identity/順序が違う".into());
        }
        let pattern = profile.pattern().ok_or("完成query patternの元表がない")?;
        if pattern.universe() != a.construction().universe() {
            return Err("query patternの共通Uが違う".into());
        }
        let mut queries = vec![];
        for query in pattern.queries() {
            tick(c)?;
            queries.push(match query {
                CircuitQuery::Atom { atom, present } => Query::Atom {
                    atom: atom.clone(),
                    present,
                },
                CircuitQuery::Relation {
                    left,
                    right,
                    present,
                } => Query::Relation {
                    left: left.clone(),
                    right: right.clone(),
                    present,
                },
                CircuitQuery::Identification {
                    left,
                    right,
                    present,
                } => Query::Identification {
                    left: left.clone(),
                    right: right.clone(),
                    present,
                },
            });
        }
        let position = base
            .checked_add(index)
            .ok_or("query patternの生成番号が域外")?;
        outputs.push(Output { universe, queries });
        rows.push(Row {
            object: *object,
            pattern: NodeRef(position),
        });
    }
    tick(c)?;
    Ok(Some((
        profiles,
        outputs,
        Diagram {
            architecture: *objects
                .architectures
                .first()
                .ok_or("query patternのbase Architectureがない")?,
            universe,
            rows,
        },
    )))
}
impl Data {
    pub(super) fn same_pattern(&self, other: &Self) -> bool {
        self.output == other.output
    }
    pub(super) fn ty(&self) -> NodeType {
        NodeType::Construction(T::CircuitPattern)
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        let mut rs = vec![
            self.source.reference,
            self.source.components,
            self.source.universe,
        ];
        rs.extend(self.source.objects.objects.iter().copied());
        rs.extend(self.source.objects.architectures.iter().copied());
        rs.sort_by_key(|r| r.0);
        rs.dedup();
        rs
    }
    pub(super) fn wire(&self) -> Json {
        self.output.wire()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.source.support.clone(), self.source.scope.clone())
    }
    pub(super) fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        if self.index >= self.source.outputs.len()
            || self.source.base.checked_add(self.index) != Some(at)
            || self.arguments().iter().any(|r| r.0 >= at)
        {
            return Err("query patternの元生成位置/既出参照が違う".into());
        }
        Ok(())
    }
}
pub(super) fn retain(
    env: &Environment<'_>,
    g: &mut Graph,
    inputs: Arc<CheckedInputs>,
    reference: NodeRef,
    components: Option<NodeRef>,
    c: &mut Control,
) -> Result<Option<Diagram>, ValidationFailure> {
    tick(c)?;
    if g.active != g.context_at(reference.0) {
        return Err("query patternの生成が元ArchitectureのRequestでない".into());
    }
    let Some((a, components, objects, universe, support, scope)) =
        original(env, g, &inputs, reference, components, c)?
    else {
        return Ok(None);
    };
    let base = g.nodes.len();
    let Some((profiles, outputs, diagram)) = compute(&inputs, &a, &objects, universe, base, c)?
    else {
        return Ok(None);
    };
    let source = Arc::new(Source {
        inputs,
        architecture: a.clone(),
        reference,
        components,
        objects,
        universe,
        profiles,
        base,
        outputs,
        diagram,
        support,
        scope,
    });
    for (index, output) in source.outputs.iter().enumerate() {
        tick(c)?;
        let data = Data {
            source: source.clone(),
            index,
            output: output.clone(),
        };
        data.position(g.nodes.len())?;
        native::retain(
            g,
            ConstructionValue {
                witness: Witness::Architecture(a.clone()),
                data: D::CircuitPattern(data),
            },
            vec![],
            vec![],
            None,
        )?;
    }
    tick(c)?;
    Ok(Some(source.diagram.clone()))
}
pub(super) fn validate_node(g: &Graph, n: &Node, data: &Data) -> Result<(), ValidationFailure> {
    let Some(Payload::Construction(value)) = &n.payload else {
        return Err("query patternのnative値がない".into());
    };
    let Witness::Architecture(a) = &value.witness else {
        return Err("query patternのconsumerが別種".into());
    };
    let owner = native::architecture_origin(g, data.source.reference, 0)?;
    let (support, scope) = data.metadata();
    if !Arc::ptr_eq(a, owner)
        || !Arc::ptr_eq(a, &data.source.architecture)
        || data.source.outputs.get(data.index) != Some(&data.output)
        || n.ty != data.ty()
        || n.rule != Rule::Construction("circuit_pattern")
        || n.arguments != data.arguments()
        || n.support != support
        || n.scope != scope
        || !n.reasons.is_empty()
        || !n.evidence.is_empty()
        || n.judgment.is_some()
    {
        return Err("query patternの全query/元由来/型/辺/metadataが違う".into());
    }
    for r in data.arguments() {
        g.tick()?;
        g.get(r)?;
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_circuit_pattern(
        &self,
        g: &Graph,
        value: &ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        let D::CircuitPattern(data) = &value.data else {
            return Ok(());
        };
        let Witness::Architecture(a) = &value.witness else {
            return Err("query patternのconsumerが別種".into());
        };
        let mut c = self.control.clone();
        let Some((owner, components, objects, universe, support, scope)) = original(
            self,
            g,
            self.indexes.inputs,
            data.source.reference,
            Some(data.source.components),
            &mut c,
        )?
        else {
            return Err("query patternの元対象が未完成".into());
        };
        if !Arc::ptr_eq(a, &owner)
            || !Arc::ptr_eq(a, &data.source.architecture)
            || objects != data.source.objects
            || components != data.source.components
            || universe != data.source.universe
            || support != data.source.support
            || scope != data.source.scope
            || self.indexes.inputs.sources() != data.source.inputs.sources()
        {
            return Err("query patternの元入力/全対象/共通U/metadataが違う".into());
        }
        if self
            .results.verified_circuit_patterns
            .borrow()
            .iter()
            .any(|s| Arc::ptr_eq(s, &data.source))
        {
            return Ok(());
        }
        let Some((profiles, outputs, diagram)) = compute(
            &data.source.inputs,
            &owner,
            &objects,
            universe,
            data.source.base,
            &mut c,
        )?
        else {
            return Err("query patternの元全表が未完成".into());
        };
        if profiles != data.source.profiles
            || outputs != data.source.outputs
            || diagram != data.source.diagram
        {
            return Err("query patternが元の全query/対象identity/対応と違う".into());
        }
        self.results.verified_circuit_patterns
            .borrow_mut()
            .push(data.source.clone());
        tick(&mut c)
    }
}
#[cfg(test)]
mod tests;
