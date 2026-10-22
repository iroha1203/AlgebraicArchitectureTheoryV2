//! 元Architectureの有限Law表示を既存のnative導出DAGへ保持する。
use super::{
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, Witness,
    },
    control::{Checkpoint, Control},
    environment::{
        Environment,
        finite_law_valuations::object::instances::realizations::automatic::{
            AutomaticLawValuations, finite_automatic_law_family,
        },
    },
    input::CheckedInputs,
    result::*,
};
use crate::{archmap::Slot, canonical::Json, types::Type};
use std::sync::Arc;

fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteLawFunction)?;
    Ok(())
}
fn refs(values: &[NodeRef]) -> Json {
    Json::Arr(values.iter().map(|r| r.wire()).collect())
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Part {
    Scalar(Scalar),
    Domain {
        ty: Type,
        elements: Vec<NodeRef>,
    },
    IntegerRing,
    FunctionRing {
        domain: NodeRef,
    },
    Function {
        ring: NodeRef,
        values: Vec<NodeRef>,
    },
    Evaluation {
        source: NodeRef,
        target: NodeRef,
        basis_images: Vec<NodeRef>,
    },
    Ideal {
        ring: NodeRef,
        generators: Vec<NodeRef>,
        required: bool,
    },
}
impl Part {
    fn ty(&self) -> NodeType {
        match self {
            Self::Scalar(v) => NodeType::Value(v.ty()),
            Self::Domain { .. } => NodeType::Domain,
            Self::IntegerRing | Self::FunctionRing { .. } => NodeType::Construction(T::Ring),
            Self::Function { .. } => NodeType::Construction(T::FiniteFunction),
            Self::Evaluation { .. } => NodeType::Construction(T::RingMap),
            Self::Ideal { .. } => NodeType::Construction(T::Ideal),
        }
    }
    fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Scalar(_) | Self::IntegerRing => vec![],
            Self::Domain { elements, .. } => elements.clone(),
            Self::FunctionRing { domain } => vec![*domain],
            Self::Function { ring, values }
            | Self::Ideal {
                ring,
                generators: values,
                ..
            } => std::iter::once(*ring)
                .chain(values.iter().copied())
                .collect(),
            Self::Evaluation {
                source,
                target,
                basis_images,
            } => [*source, *target]
                .into_iter()
                .chain(basis_images.iter().copied())
                .collect(),
        }
    }
    fn construction(&self) -> &'static str {
        match self {
            Self::Scalar(_) => "binding",
            Self::Domain { .. } => "domain",
            Self::IntegerRing | Self::FunctionRing { .. } => "ring",
            Self::Function { .. } => "finite_function",
            Self::Evaluation { .. } => "ring_map",
            Self::Ideal { .. } => "ideal",
        }
    }
    fn wire(&self) -> Json {
        match self {
            Self::Scalar(v) => v.wire(),
            Self::Domain { ty, elements } => Json::obj([
                ("kind", Json::str("finite")),
                ("type", ty.wire()),
                ("elements", refs(elements)),
            ]),
            Self::IntegerRing => {
                Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str("Z"))])
            }
            Self::FunctionRing { domain } => Json::obj([
                ("kind", Json::str("finite_functions")),
                ("domain", domain.wire()),
            ]),
            Self::Function { ring, values } => {
                Json::obj([("ring", ring.wire()), ("values", refs(values))])
            }
            Self::Evaluation {
                source,
                target,
                basis_images,
            } => Json::obj([
                ("kind", Json::str("finite_functions")),
                ("source", source.wire()),
                ("target", target.wire()),
                ("basis_images", refs(basis_images)),
            ]),
            Self::Ideal {
                ring,
                generators,
                required,
            } => Json::obj([
                ("ring", ring.wire()),
                ("generators", refs(generators)),
                (
                    "kind",
                    Json::str(if *required { "obstruction" } else { "witness" }),
                ),
            ]),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Diagram {
    pub points: Vec<usize>,
    pub domain: NodeRef,
    pub ring: NodeRef,
    pub target: NodeRef,
    pub evaluation: Option<NodeRef>,
    pub columns: Vec<usize>,
    pub components: Vec<(usize, Option<Vec<usize>>)>,
    pub nu: Vec<NodeRef>,
    pub epsilon: Vec<Option<NodeRef>>,
    pub witnesses: Vec<NodeRef>,
    pub required: NodeRef,
}
#[derive(Clone)]
pub(super) struct Source {
    inputs: Arc<CheckedInputs>,
    architecture: Arc<ArchitectureWitness>,
    reference: NodeRef,
    object: usize,
    base: usize,
    parts: Vec<Part>,
    outputs: Diagram,
    support: Vec<Fact>,
    scope: Scope,
}
impl std::fmt::Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FiniteLawDiagramSource")
            .field("reference", &self.reference)
            .field("object", &self.object)
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
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.source, &other.source) && self.index == other.index
    }
}
impl Eq for Data {}
impl Data {
    fn part(&self) -> &Part {
        &self.source.parts[self.index]
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        match self.source.parts.get(self.index) {
            Some(Part::Scalar(v)) => Some(v),
            _ => None,
        }
    }
    pub(super) fn ty(&self) -> NodeType {
        self.part().ty()
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part().construction()
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        std::iter::once(self.source.reference)
            .chain(self.part().arguments())
            .collect()
    }
    pub(super) fn wire(&self) -> Json {
        self.part().wire()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.source.support.clone(), self.source.scope.clone())
    }
    pub(super) fn position(&self, position: usize) -> Result<(), ValidationFailure> {
        if self.index >= self.source.parts.len()
            || self.source.base.checked_add(self.index) != Some(position)
        {
            return Err("有限Law導出の元計画・生成位置が違う".into());
        }
        Ok(())
    }
}
fn push(parts: &mut Vec<Part>, base: usize, part: Part) -> Result<NodeRef, ValidationFailure> {
    let index = base
        .checked_add(parts.len())
        .ok_or("有限Law導出の番号が範囲外")?;
    parts.push(part);
    Ok(NodeRef(index))
}
fn function(
    parts: &mut Vec<Part>,
    base: usize,
    ring: NodeRef,
    values: &[num_bigint::BigInt],
    points: &[usize],
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let mut elements = vec![];
    if points.len() != values.len() {
        return Err("有限Lawの公開順と関数の次元が違う".into());
    }
    for point in points {
        tick(c)?;
        let v = values.get(*point).ok_or("有限Lawの元関数座標が範囲外")?;
        elements.push(push(parts, base, Part::Scalar(Scalar::Z(v.clone())))?);
    }
    push(
        parts,
        base,
        Part::Function {
            ring,
            values: elements,
        },
    )
}
fn plan(
    f: &AutomaticLawValuations,
    inputs: &CheckedInputs,
    object: usize,
    base: usize,
    c: &mut Control,
) -> Result<(Vec<Part>, Diagram), ValidationFailure> {
    tick(c)?;
    let p = f
        .object_presentation(inputs, object, c)?
        .ok_or("有限Lawの元表示が未完成")?;
    // 元の所属条件を満たすDは変えず、原始値のencodingだけをRefへ表す。
    let mut value_types = vec![];
    for ty in f.types() {
        tick(c)?;
        value_types.push(
            ty.erase_controlled::<super::control::CheckFailure<Box<crate::issue::Issue>>>(
                c,
                Checkpoint::FiniteLawFunction,
            )
            .map_err(|e| match e {
                super::control::CheckFailure::Stopped(stop) => ValidationFailure::Stop(stop),
                super::control::CheckFailure::Input(_) => {
                    ValidationFailure::Internal("有限Lawの原始表示型が解決できない".into())
                }
            })?,
        );
    }
    let ty = match value_types.as_slice() {
        [] => Type::Unit,
        [ty] => ty.clone(),
        items => Type::Tuple(items.to_vec()),
    };
    let mut ordered = vec![];
    for (point, values) in f.domain().iter().enumerate() {
        tick(c)?;
        let value = match values.as_slice() {
            [] => Scalar::Unit,
            [v] => v.clone(),
            items => Scalar::Tuple(items.to_vec()),
        };
        if value.ty() != ty {
            return Err("有限Lawの全Dの型が違う".into());
        }
        let key = value
            .wire()
            .canonical_controlled::<super::control::CheckFailure<Box<crate::issue::Issue>>>(
                c,
                Checkpoint::FiniteLawFunction,
            )
            .map_err(|e| match e {
                super::control::CheckFailure::Stopped(stop) => ValidationFailure::Stop(stop),
                super::control::CheckFailure::Input(_) => {
                    ValidationFailure::Internal("有限Lawのcanonical値が構成できない".into())
                }
            })?;
        ordered.push((key, point, value));
    }
    // 内部の数値/直積順を変えず、公開集合表のUTF-8 byte辞書順と対応させる。
    ordered.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    tick(c)?;
    for pair in ordered.windows(2) {
        tick(c)?;
        if pair[0].0 == pair[1].0 {
            return Err("有限Lawの公開Dに重複した値がある".into());
        }
    }
    let mut points = vec![];
    let mut parts = vec![];
    let mut elements = vec![];
    for (_, point, value) in ordered {
        tick(c)?;
        points.push(point);
        elements.push(push(&mut parts, base, Part::Scalar(value))?);
    }
    let domain = push(&mut parts, base, Part::Domain { ty, elements })?;
    let ring = push(&mut parts, base, Part::FunctionRing { domain })?;
    let target = push(&mut parts, base, Part::IntegerRing)?;
    let evaluation = if let Some(ev) = f.object_evaluation(c)? {
        let mut images = vec![];
        for point in &points {
            tick(c)?;
            let v = ev
                .basis_images()
                .get(*point)
                .ok_or("有限Lawの元評価座標が範囲外")?;
            images.push(push(&mut parts, base, Part::Scalar(Scalar::Z(v.clone())))?);
        }
        Some(push(
            &mut parts,
            base,
            Part::Evaluation {
                source: ring,
                target,
                basis_images: images,
            },
        )?)
    } else {
        None
    };
    let mut columns = vec![];
    let mut components = vec![];
    let mut nu = vec![];
    let mut epsilon = vec![];
    let mut witnesses = vec![];
    for (index, eq) in p.equations().iter().enumerate() {
        tick(c)?;
        columns.push(eq.column());
        components.push((eq.instance(), eq.component().map(<[usize]>::to_vec)));
        let symbol = function(&mut parts, base, ring, eq.nu().values(), &points, c)?;
        nu.push(symbol);
        epsilon.push(
            eq.constant()
                .map(|value| function(&mut parts, base, ring, value.values(), &points, c))
                .transpose()?,
        );
        let ideal = p.witness_ideal(index, c)?;
        if ideal.equations() != [index] {
            return Err("有限witnessの元成分が違う".into());
        }
        witnesses.push(push(
            &mut parts,
            base,
            Part::Ideal {
                ring,
                generators: vec![symbol],
                required: false,
            },
        )?);
    }
    let required = p.required_ideal(c)?;
    let mut generators = vec![];
    for index in required.equations() {
        tick(c)?;
        generators.push(*nu.get(*index).ok_or("requiredの元νがない")?);
    }
    let required = push(
        &mut parts,
        base,
        Part::Ideal {
            ring,
            generators,
            required: true,
        },
    )?;
    tick(c)?;
    Ok((
        parts,
        Diagram {
            points,
            domain,
            ring,
            target,
            evaluation,
            columns,
            components,
            nu,
            epsilon,
            witnesses,
            required,
        },
    ))
}
fn metadata(
    inputs: &CheckedInputs,
    a: &Arc<ArchitectureWitness>,
    f: &AutomaticLawValuations,
    c: &mut Control,
) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
    let value = ConstructionValue {
        witness: Witness::Architecture(a.clone()),
        data: D::ConstructionLabel(Scalar::Text("finite_law".into())),
    };
    let (mut support, mut scope) = native::metadata(&value)?;
    let env = Environment::new(inputs, c)?;
    for position in f.positions() {
        tick(c)?;
        let field = env.field(
            &position.snapshot,
            &position.subject,
            position.field.as_deref().ok_or("有限Lawの元fieldがない")?,
        )?;
        let mut fact = position.clone();
        if let Slot::Known { atom, .. } = &field.slot {
            fact.atom = Some(atom.clone());
            let value = native::atom_value(Witness::Architecture(a.clone()), &fact, c)?;
            let (facts, s) = native::metadata(&value)?;
            support.extend(facts);
            scope.merge(&s);
        } else {
            fact.field = None;
            fact.atom = None;
            let value = native::subject_value(Witness::Architecture(a.clone()), &fact)?;
            let (facts, s) = native::metadata(&value)?;
            support.extend(facts);
            scope.merge(&s);
        }
    }
    support.sort_by_key(|f| f.wire().canonical());
    support.dedup();
    scope.assignments = true;
    tick(c)?;
    Ok((support, scope))
}
impl Source {
    fn compute(
        inputs: Arc<CheckedInputs>,
        architecture: Arc<ArchitectureWitness>,
        reference: NodeRef,
        object: usize,
        base: usize,
        c: &mut Control,
    ) -> Result<Option<Self>, ValidationFailure> {
        tick(c)?;
        if Witness::Architecture(architecture.clone())
            .inputs()
            .sources()
            != inputs.sources()
        {
            return Err("有限Lawの三入力とArchitectureが違う".into());
        }
        architecture
            .readings()
            .objects()
            .get(object)
            .ok_or("有限Lawの対象が範囲外")?;
        let full = finite_automatic_law_family(&inputs, architecture.readings(), c)
            .map_err(|e| e.cause)?;
        let Some(f) = full.family() else {
            return Ok(None);
        };
        if !f.is_complete() || !f.domain_complete() {
            return Ok(None);
        }
        let (parts, outputs) = plan(f, &inputs, object, base, c)?;
        let (support, scope) = metadata(&inputs, &architecture, f, c)?;
        tick(c)?;
        Ok(Some(Self {
            inputs,
            architecture,
            reference,
            object,
            base,
            parts,
            outputs,
            support,
            scope,
        }))
    }
    fn recheck(
        &self,
        inputs: &CheckedInputs,
        architecture: &Arc<ArchitectureWitness>,
        object: usize,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        tick(c)?;
        if !Arc::ptr_eq(architecture, &self.architecture)
            || object != self.object
            || inputs.sources() != self.inputs.sources()
        {
            return Err("有限Law導出の消費先Architecture・対象・三入力が違う".into());
        }
        architecture
            .readings()
            .recheck(inputs, c)
            .map_err(|e| match e {
                crate::construction::ConstructionFailure::Stopped(s) => ValidationFailure::Stop(s),
                other => format!("有限Lawの元reading: {other:?}").into(),
            })?;
        let other = Self::compute(
            self.inputs.clone(),
            architecture.clone(),
            self.reference,
            object,
            self.base,
            c,
        )?
        .ok_or("有限Law導出の元族が未完成")?;
        if self.parts != other.parts
            || self.outputs != other.outputs
            || self.support != other.support
            || self.scope != other.scope
        {
            return Err("有限Law導出が元全D・成分・生成元・支持と違う".into());
        }
        tick(c)
    }
}
pub(super) fn retain(
    graph: &mut Graph,
    inputs: Arc<CheckedInputs>,
    architecture: NodeRef,
    object: usize,
    c: &mut Control,
) -> Result<Option<Diagram>, ValidationFailure> {
    tick(c)?;
    let Some(Payload::Construction(v)) = &graph.get(architecture)?.payload else {
        return Err("有限Lawの元Architectureがない".into());
    };
    let (Witness::Architecture(a), D::Architecture { .. }) = (&v.witness, &v.data) else {
        return Err("有限Lawの元参照が完成Architectureでない".into());
    };
    let context = graph.context_at(architecture.0);
    if graph.active != context
        || context.frame.is_some()
        || context.iteration.is_some()
        || context.instance.is_some()
        || context.case.is_some()
        || graph.requests.get(context.request) != Some(Witness::Architecture(a.clone()).request())
    {
        return Err("有限Law導出が元Architectureのroot Requestでない".into());
    }
    let Some(source) = Source::compute(
        inputs,
        a.clone(),
        architecture,
        object,
        graph.nodes.len(),
        c,
    )?
    else {
        return Ok(None);
    };
    let source = Arc::new(source);
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
                data: D::FiniteLaw(data),
            },
            vec![],
            vec![],
            None,
        )?;
    }
    tick(c)?;
    Ok(Some(source.outputs.clone()))
}
pub(super) fn validate_node(graph: &Graph, n: &Node, data: &Data) -> Result<(), ValidationFailure> {
    let Some(part) = data.source.parts.get(data.index) else {
        return Err("有限Lawの元計画添字がない".into());
    };
    let Some(Payload::Construction(v)) = &n.payload else {
        return Err("有限Law導出payloadがない".into());
    };
    let Witness::Architecture(a) = &v.witness else {
        return Err("有限Lawの元Architectureがない".into());
    };
    let Some(Payload::Construction(origin)) = &graph.get(data.source.reference)?.payload else {
        return Err("有限Lawの元参照がない".into());
    };
    if !matches!((&origin.witness,&origin.data),(Witness::Architecture(b),D::Architecture{..}) if Arc::ptr_eq(a,b)&&Arc::ptr_eq(a,&data.source.architecture))
    {
        return Err("有限Lawの元Architecture参照が違う".into());
    }
    if n.ty != part.ty()
        || n.rule != Rule::Construction(part.construction())
        || n.arguments != data.arguments()
        || n.support != data.source.support
        || n.scope != data.source.scope
        || !n.reasons.is_empty()
        || !n.evidence.is_empty()
        || n.judgment.is_some()
    {
        return Err("有限Lawの型・導出・原始支持・scopeが違う".into());
    }
    for reference in part.arguments() {
        let child = graph.get(reference)?;
        let Some(Payload::Construction(v)) = &child.payload else {
            return Err("有限Lawの構成引数がnativeでない".into());
        };
        let D::FiniteLaw(other) = &v.data else {
            return Err("有限Lawの構成引数が別由来".into());
        };
        if !Arc::ptr_eq(&data.source, &other.source)
            || other.index >= data.index
            || data.source.base.checked_add(other.index) != Some(reference.0)
        {
            return Err("有限Lawの構成引数が元計画の既出値でない".into());
        }
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_finite_law_diagram(
        &self,
        graph: &Graph,
        value: &ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        let D::FiniteLaw(data) = &value.data else {
            return Ok(());
        };
        tick(&mut self.control.clone())?;
        let Witness::Architecture(a) = &value.witness else {
            return Err("有限Law導出の元Architectureがない".into());
        };
        let Some(Payload::Construction(v)) = &graph.get(data.source.reference)?.payload else {
            return Err("有限Lawの元参照がない".into());
        };
        if !matches!((&v.witness,&v.data),(Witness::Architecture(b),D::Architecture{..}) if Arc::ptr_eq(a,b)&&Arc::ptr_eq(a,&data.source.architecture))
        {
            return Err("有限Lawの消費先Architectureが違う".into());
        }
        // immutable Arcを保持し、別のreading/根の検査成功を再利用しない。
        if self
            .verified_finite_law_diagrams
            .borrow()
            .iter()
            .any(|s| Arc::ptr_eq(s, &data.source))
        {
            return Ok(());
        }
        data.source.recheck(
            self.inputs,
            a,
            data.source.object,
            &mut self.control.clone(),
        )?;
        self.verified_finite_law_diagrams
            .borrow_mut()
            .push(data.source.clone());
        Ok(())
    }
}
#[cfg(test)]
#[path = "finite_law_diagram_tests.rs"]
mod tests;
