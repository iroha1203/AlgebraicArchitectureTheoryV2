//! 標準対象族のidentityと部分構成を、元Architectureに由来するDAGへ保持する。
use super::{
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, Witness,
    },
    control::{Checkpoint, Control},
    environment::Environment,
    input::CheckedInputs,
    result::*,
};
use crate::{
    canonical::Json,
    construction::{Configuration, readings::InstanceApplication},
    law::model::Signature,
    types::Type,
};
use std::sync::Arc;

fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectInstances)?;
    Ok(())
}
fn refs(values: &[NodeRef]) -> Json {
    Json::Arr(values.iter().map(|r| r.wire()).collect())
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Part {
    Reading {
        object: NodeRef,
        declaration: String,
        parameters: Vec<(String, Type)>,
        bindings: Vec<Binding>,
        returns: Type,
        quantifiers: Vec<Quantifier>,
    },
    Subject(Scalar),
    Configuration(Configuration),
    Architecture {
        reading: String,
        root: NodeRef,
        configuration: NodeRef,
        laws: Vec<NodeRef>,
    },
    Component {
        base: bool,
        subject: NodeRef,
        object: NodeRef,
    },
}
impl Part {
    fn ty(&self) -> NodeType {
        match self {
            Self::Subject(v) => NodeType::Value(v.ty()),
            Self::Reading { returns, .. } => NodeType::Expression(returns.clone()),
            Self::Configuration(_) => NodeType::Construction(T::Configuration),
            Self::Architecture { .. } => NodeType::Construction(T::Architecture),
            Self::Component { .. } => NodeType::Construction(T::ObjectComponent),
        }
    }
    fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Subject(_) | Self::Configuration(_) => vec![],
            Self::Reading {
                object, bindings, ..
            } => std::iter::once(*object)
                .chain(bindings.iter().map(|b| b.value))
                .collect(),
            Self::Architecture {
                root,
                configuration,
                laws,
                ..
            } => std::iter::once(*root)
                .chain(std::iter::once(*configuration))
                .chain(laws.iter().copied())
                .collect(),
            Self::Component {
                subject, object, ..
            } => vec![*subject, *object],
        }
    }
    fn construction(&self) -> &'static str {
        match self {
            Self::Subject(_) => "binding",
            Self::Reading { .. } => "expression",
            Self::Configuration(_) => "configuration",
            Self::Architecture { .. } => "architecture",
            Self::Component { .. } => "object_component",
        }
    }
    fn wire(&self) -> Json {
        match self {
            Self::Subject(v) => v.wire(),
            Self::Reading {
                object,
                declaration,
                parameters,
                bindings,
                returns,
                ..
            } => Json::obj([
                ("kind", Json::str("object_reading")),
                ("object", object.wire()),
                ("declaration", Json::str(declaration)),
                (
                    "parameters",
                    Json::Arr(
                        parameters
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
                        bindings
                            .iter()
                            .map(|b| {
                                Json::obj([("name", Json::str(&b.name)), ("value", b.value.wire())])
                            })
                            .collect(),
                    ),
                ),
                ("returns", returns.wire()),
            ]),
            Self::Configuration(v) => v.wire(),
            Self::Architecture {
                reading,
                root,
                configuration,
                laws,
            } => Json::obj([
                ("reading", Json::str(reading)),
                ("root", root.wire()),
                ("configuration", configuration.wire()),
                ("laws", refs(laws)),
                ("internal_arrows", Json::Arr(vec![])),
                ("overrides", Json::Arr(vec![])),
            ]),
            Self::Component {
                base,
                subject,
                object,
            } => Json::obj([
                ("kind", Json::str(if *base { "base" } else { "owned" })),
                ("subject", subject.wire()),
                ("object", object.wire()),
            ]),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Diagram {
    /// 元ObjectReadingInstances.objectsと同じ順。
    pub objects: Vec<NodeRef>,
    pub architectures: Vec<NodeRef>,
    pub base: NodeRef,
    pub readings: Vec<Reading>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Reading {
    pub object: usize,
    pub instance: usize,
    pub expression: NodeRef,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ViewOrigin {
    pub expression: NodeRef,
    pub component: NodeRef,
    pub architecture: NodeRef,
    pub declaration: String,
    pub bindings: Vec<Binding>,
    pub parameters: Vec<(String, Type)>,
    pub returns: Type,
    pub body: usize,
    pub application: InstanceApplication,
}
#[derive(Clone)]
pub(super) struct Source {
    inputs: Arc<CheckedInputs>,
    architecture: Arc<ArchitectureWitness>,
    reference: NodeRef,
    root: NodeRef,
    laws: Vec<NodeRef>,
    base: usize,
    parts: Vec<Part>,
    outputs: Diagram,
    support: Vec<Fact>,
    scope: Scope,
}
impl std::fmt::Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ObjectComponentSource")
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
    pub(super) fn view_origin(
        &self,
        reference: NodeRef,
    ) -> Result<Option<(Arc<ArchitectureWitness>, ViewOrigin)>, ValidationFailure> {
        self.position(reference.0)?;
        let Part::Reading {
            object,
            declaration,
            parameters,
            bindings,
            returns,
            ..
        } = self.part()
        else {
            return Ok(None);
        };
        let reading = self
            .source
            .outputs
            .readings
            .iter()
            .find(|r| r.expression == reference)
            .ok_or("view式が元対象表にない")?;
        let a = &self.source.architecture;
        let row = a
            .readings()
            .instances()
            .get(reading.instance)
            .ok_or("viewの元instanceがない")?;
        let input = Witness::Architecture(a.clone());
        let original = input
            .inputs()
            .law()
            .declarations
            .get(declaration)
            .ok_or("元view宣言がない")?;
        let Signature::View { body, .. } = &original.signature else {
            return Ok(None);
        };
        let architecture = *self
            .source
            .outputs
            .architectures
            .get(reading.object)
            .ok_or("viewの対象Architectureがない")?;
        if self.source.outputs.objects.get(reading.object) != Some(object)
            || row.declaration().name != *declaration
        {
            return Err("viewの元対象/宣言対応が違う".into());
        }
        Ok(Some((
            a.clone(),
            ViewOrigin {
                expression: reference,
                component: *object,
                architecture,
                declaration: declaration.clone(),
                bindings: bindings.clone(),
                parameters: parameters.clone(),
                returns: returns.clone(),
                body: *body,
                application: row
                    .applications()
                    .get(reading.object)
                    .ok_or("viewの対象別適用がない")?
                    .clone(),
            },
        )))
    }
    pub(super) fn retained_components(&self) -> (Arc<ArchitectureWitness>, NodeRef, Diagram) {
        (
            self.source.architecture.clone(),
            self.source.reference,
            self.source.outputs.clone(),
        )
    }
    fn part(&self) -> &Part {
        &self.source.parts[self.index]
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        match self.source.parts.get(self.index) {
            Some(Part::Subject(v)) => Some(v),
            _ => None,
        }
    }
    pub(super) fn root_type(&self) -> Option<String> {
        let root = self.root()?;
        let Part::Subject(Scalar::Subject { entity, .. }) = self.source.parts.get(root.0.checked_sub(self.source.base)?)? else {
            return None;
        };
        Some(entity.clone())
    }
    pub(super) fn root(&self) -> Option<NodeRef> {
        match self.source.parts.get(self.index)? {
            Part::Architecture { root, .. } => Some(*root),
            _ => None,
        }
    }
    /// 呼出し側は元nodeの検査を先に行う。対象番号は元計画の対応表からだけ復元する。
    pub(super) fn architecture_object(
        &self,
        reference: NodeRef,
    ) -> Result<usize, ValidationFailure> {
        self.position(reference.0)?;
        if !matches!(
            self.source.parts.get(self.index),
            Some(Part::Architecture { .. })
        ) {
            return Err("評価環境が標準対象族のArchitectureでない".into());
        }
        self.source
            .outputs
            .architectures
            .iter()
            .position(|r| *r == reference)
            .ok_or_else(|| "評価環境のArchitectureが元の対象表にない".into())
    }
    pub(super) fn ty(&self) -> NodeType {
        self.part().ty()
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        std::iter::once(self.source.reference)
            .chain(self.part().arguments())
            .collect()
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part().construction()
    }
    pub(super) fn wire(&self) -> Json {
        self.part().wire()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        let mut scope = self.source.scope.clone();
        if let Part::Reading { quantifiers, .. } = self.part() {
            scope.quantifiers.extend_from_slice(quantifiers);
        }
        (self.source.support.clone(), scope)
    }
    pub(super) fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        if self.index >= self.source.parts.len()
            || self.source.base.checked_add(self.index) != Some(at)
        {
            return Err("対象族の生成位置が元計画と違う".into());
        }
        Ok(())
    }
}
fn push(
    parts: &mut Vec<Part>,
    base: usize,
    value: Part,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    tick(c)?;
    let reference = base
        .checked_add(parts.len())
        .ok_or("対象族の生成番号が範囲外")?;
    parts.push(value);
    Ok(NodeRef(reference))
}
fn plan(
    inputs: &CheckedInputs,
    a: &ArchitectureWitness,
    reference: NodeRef,
    root: NodeRef,
    laws: &[NodeRef],
    base: usize,
    c: &mut Control,
) -> Result<Option<(Vec<Part>, Diagram)>, ValidationFailure> {
    tick(c)?;
    let construction = a.construction();
    if construction.base().configuration().is_none() || !construction.local_domain().is_complete() {
        return Ok(None);
    }
    let readings = a.readings();
    if readings.objects().len() != construction.components().len() + 1 {
        return Err("対象族と元部分構成の件数が違う".into());
    }
    let law_indices: Vec<_> = readings
        .instances()
        .iter()
        .enumerate()
        .filter(|(_, row)| row.declaration().kind == "law")
        .map(|(i, _)| i)
        .collect();
    if law_indices.len() != laws.len() {
        return Err("対象族の元Law族の件数が違う".into());
    }
    let mut parts = vec![];
    let mut objects = vec![];
    let mut architectures = vec![];
    let mut seen = std::collections::BTreeSet::new();
    for (index, selected) in readings.objects().iter().enumerate() {
        tick(c)?;
        let identity = selected.identity();
        if identity.reading() != construction.reading()
            || identity.root() != construction.root()
            || !selected.conditions().is_empty()
        {
            return Ok(None);
        }
        if !seen.insert(identity.subject().clone()) {
            return Err("対象族のsubject identityが重複する".into());
        }
        let is_base = identity.subject() == construction.root();
        if is_base != (index == 0) {
            return Err("対象族のbaseの元順序が違う".into());
        }
        let (subject, architecture) = if is_base {
            (root, reference)
        } else {
            let component = construction
                .components()
                .iter()
                .find(|p| p.subject() == identity.subject())
                .ok_or("対象族の元部分構成がない")?;
            let Some(configuration) = component.candidate().configuration() else {
                return Ok(None);
            };
            let fact = identity.subject();
            let original = inputs
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == fact.snapshot)
                .and_then(|s| s.subjects.iter().find(|s| s.id == fact.subject))
                .ok_or("部分対象の元subjectがない")?;
            let subject = push(
                &mut parts,
                base,
                Part::Subject(Scalar::Subject {
                    snapshot: fact.snapshot.clone(),
                    subject: fact.subject.clone(),
                    entity: original.ty.clone(),
                }),
                c,
            )?;
            let configuration = push(
                &mut parts,
                base,
                Part::Configuration(configuration.clone()),
                c,
            )?;
            let mut selected_laws = vec![];
            for (&law, &instance) in laws.iter().zip(&law_indices) {
                tick(c)?;
                let row = &readings.instances()[instance];
                match row
                    .applications()
                    .get(index)
                    .ok_or("部分対象のLaw適用行がない")?
                {
                    InstanceApplication::NotApplicable => {}
                    InstanceApplication::Applicable { conditions } if conditions.is_empty() => {
                        selected_laws.push(law)
                    }
                    InstanceApplication::Applicable { .. } => return Ok(None),
                }
            }
            let architecture = push(
                &mut parts,
                base,
                Part::Architecture {
                    reading: construction.reading().into(),
                    root: subject,
                    configuration,
                    laws: selected_laws,
                },
                c,
            )?;
            (subject, architecture)
        };
        let object = push(
            &mut parts,
            base,
            Part::Component {
                base: is_base,
                subject,
                object: architecture,
            },
            c,
        )?;
        objects.push(object);
        architectures.push(architecture);
    }
    let reading_expressions = reading_plan(inputs, a, &objects, &mut parts, base, c)?;
    let base = *objects.first().ok_or("対象族にbaseがない")?;
    tick(c)?;
    Ok(Some((
        parts,
        Diagram {
            objects,
            architectures,
            base,
            readings: reading_expressions,
        },
    )))
}
fn primitive(ty: &Type, c: &mut Control) -> Result<Type, ValidationFailure> {
    ty.erase_controlled::<super::control::CheckFailure<Box<crate::issue::Issue>>>(
        c,
        Checkpoint::ObjectInstances,
    )
    .map_err(|e| match e {
        super::control::CheckFailure::Stopped(s) => ValidationFailure::Stop(s),
        super::control::CheckFailure::Input(_) => "対象読取りの原始型がない".into(),
    })
}
fn reading_plan(
    inputs: &CheckedInputs,
    a: &ArchitectureWitness,
    objects: &[NodeRef],
    parts: &mut Vec<Part>,
    base: usize,
    c: &mut Control,
) -> Result<Vec<Reading>, ValidationFailure> {
    let mut outputs = vec![];
    for (instance, row) in a.readings().instances().iter().enumerate() {
        tick(c)?;
        let declaration = inputs
            .law()
            .declarations
            .get(&row.declaration().name)
            .ok_or("対象読取りの元宣言がない")?;
        let (params, returns) = match &declaration.signature {
            Signature::Law { params, .. } => (params, Type::Bool),
            Signature::View {
                params, returns, ..
            } => (params, Type::Option(Box::new(primitive(returns, c)?))),
            _ => return Err("対象読取りの元宣言がLaw/viewでない".into()),
        };
        let mut bindings = vec![];
        let mut parameters = vec![];
        let mut quantifiers = vec![];
        for parameter in params {
            tick(c)?;
            let bound = row
                .bindings()
                .iter()
                .filter(|b| b.parameter().name == parameter.name)
                .collect::<Vec<_>>();
            match bound.as_slice() {
                [binding] => {
                    let entity = match &parameter.ty {
                        Type::Ref(t) | Type::Owned(t, _) => t.clone(),
                        _ => return Err("対象読取りの参照束縛型が違う".into()),
                    };
                    let subject = binding.subject();
                    let value = push(
                        parts,
                        base,
                        Part::Subject(Scalar::Subject {
                            snapshot: subject.snapshot.clone(),
                            subject: subject.subject.clone(),
                            entity: entity.clone(),
                        }),
                        c,
                    )?;
                    bindings.push(Binding {
                        name: parameter.name.clone(),
                        ty: Type::Ref(entity),
                        value,
                    });
                }
                [] => {
                    let original = row
                        .parameters()
                        .iter()
                        .find(|p| p.name == parameter.name)
                        .ok_or("対象読取りの全域parameterがない")?;
                    parameters.push((original.name.clone(), primitive(&original.ty, c)?));
                    quantifiers.push(Quantifier {
                        kind: crate::law::ast::QuantKind::Forall,
                        name: original.name.clone(),
                        ty: original.ty.clone(),
                        occurrence: original.span,
                        domain: None,
                        context: None,
                    });
                }
                _ => return Err("対象読取りの参照束縛が重複する".into()),
            }
        }
        for (object, reference) in objects.iter().enumerate() {
            tick(c)?;
            if row.applications().get(object).is_none() {
                return Err("対象読取りの元適用行がない".into());
            }
            let expression = push(
                parts,
                base,
                Part::Reading {
                    object: *reference,
                    declaration: declaration.name.clone(),
                    parameters: parameters.clone(),
                    bindings: bindings.clone(),
                    returns: returns.clone(),
                    quantifiers: quantifiers.clone(),
                },
                c,
            )?;
            outputs.push(Reading {
                object,
                instance,
                expression,
            });
        }
    }
    tick(c)?;
    Ok(outputs)
}
fn reading_metadata(
    inputs: &CheckedInputs,
    a: &Arc<ArchitectureWitness>,
    source: &Node,
    c: &mut Control,
) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
    let mut support = source.support.clone();
    let mut scope = source.scope.clone();
    let env = Environment::new(inputs, c)?;
    for row in a.readings().instances() {
        for binding in row.bindings() {
            tick(c)?;
            let subject =
                native::subject_value(Witness::Architecture(a.clone()), binding.subject())?;
            let (facts, s) = native::metadata(&subject)?;
            support.extend(facts);
            scope.merge(&s);
        }
        for parameter in row.parameters() {
            tick(c)?;
            let domain = env.object_parameter_domain(parameter, row)?;
            support.extend(domain.support);
            scope.merge(&domain.scope);
        }
    }
    support.sort_by_key(|f| f.wire().canonical());
    support.dedup();
    tick(c)?;
    Ok((support, scope))
}
fn origin<'a>(
    graph: &'a Graph,
    reference: NodeRef,
) -> Result<(&'a Arc<ArchitectureWitness>, NodeRef, &'a [NodeRef]), ValidationFailure> {
    let Some(Payload::Construction(value)) = &graph.get(reference)?.payload else {
        return Err("対象族の元Architectureがない".into());
    };
    let (Witness::Architecture(a), D::Architecture { root, laws, .. }) =
        (&value.witness, &value.data)
    else {
        return Err("対象族の元参照が完成Architectureでない".into());
    };
    let context = graph.context_at(reference.0);
    if context.frame.is_some()
        || context.iteration.is_some()
        || context.instance.is_some()
        || context.case.is_some()
        || graph.requests.get(context.request) != Some(Witness::Architecture(a.clone()).request())
    {
        return Err("対象族が元Architectureのroot Requestでない".into());
    }
    Ok((a, *root, laws))
}
/// 実際に保持した部分Architectureだけを元対象へ対応させる。
pub(super) fn architecture_origin(
    graph: &Graph,
    reference: NodeRef,
    object: usize,
) -> Result<&Arc<ArchitectureWitness>, ValidationFailure> {
    let node = graph.get(reference)?;
    let Some(Payload::Construction(value)) = &node.payload else {
        return Err("有限Lawの部分Architectureがない".into());
    };
    let D::ObjectComponents(data) = &value.data else {
        return Err("有限Lawの参照が標準対象族でない".into());
    };
    data.position(reference.0)?;
    if !matches!(
        data.source.parts.get(data.index),
        Some(Part::Architecture { .. })
    ) || data.source.outputs.architectures.get(object) != Some(&reference)
    {
        return Err("有限Lawの部分Architectureと元対象の対応が違う".into());
    }
    validate_node(graph, node, data)?;
    Ok(&data.source.architecture)
}
/// 元のbase成分から、保持済みの対象表だけを取り出す。
pub(super) fn original_family(
    graph: &Graph,
    base: NodeRef,
) -> Result<(NodeRef, Diagram), ValidationFailure> {
    let node = graph.get(base)?;
    let Some(Payload::Construction(value)) = &node.payload else {
        return Err("内部arrowの対象表がnativeでない".into());
    };
    let D::ObjectComponents(data) = &value.data else {
        return Err("内部arrowの対象表が標準対象族でない".into());
    };
    data.position(base.0)?;
    if data.source.outputs.base != base {
        return Err("内部arrowの対象表のbaseが違う".into());
    }
    let source = &data.source;
    let end = source.base.checked_add(source.parts.len())
        .ok_or("内部arrowの対象表の完了位置が範囲外")?;
    if graph.nodes.len() < end {
        return Err("内部arrowの標準対象族が保持途中".into());
    }
    let context = *graph.contexts.get(source.reference.0)
        .ok_or("内部arrowの元Architectureのcontextがない")?;
    for index in 0..source.parts.len() {
        let at = source.base.checked_add(index)
            .ok_or("内部arrowの対象表の位置が範囲外")?;
        let node = graph.get(NodeRef(at))?;
        let Some(Payload::Construction(value)) = &node.payload else {
            return Err("内部arrowの対象表が別の保持結果に置換された".into());
        };
        let D::ObjectComponents(current) = &value.data else {
            return Err("内部arrowの対象表が別由来に置換された".into());
        };
        current.position(at)?;
        if !Arc::ptr_eq(source, &current.source) || current.index != index
            || graph.contexts.get(at) != Some(&context)
        {
            return Err("内部arrowの対象表の位置・由来・contextが違う".into());
        }
        validate_node(graph, node, current)?;
    }
    Ok((source.reference, source.outputs.clone()))
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
        let (current, root, laws) = origin(graph, self.reference)?;
        if inputs.sources() != self.inputs.sources()
            || inputs.sources() != Witness::Architecture(a.clone()).inputs().sources()
            || !Arc::ptr_eq(a, current)
            || !Arc::ptr_eq(a, &self.architecture)
            || root != self.root
            || laws != self.laws
        {
            return Err("対象族の元三入力・consumer・根・Law参照が違う".into());
        }
        let construction = a.construction();
        construction
            .recheck(
                inputs,
                construction.reading(),
                &construction.root().snapshot,
                &construction.root().subject,
                c,
            )
            .map_err(|e| match e {
                crate::construction::ConstructionFailure::Stopped(s) => ValidationFailure::Stop(s),
                other => format!("対象族の構成: {other:?}").into(),
            })?;
        a.readings().recheck(inputs, c).map_err(|e| match e {
            crate::construction::ConstructionFailure::Stopped(s) => ValidationFailure::Stop(s),
            other => format!("対象族の適用: {other:?}").into(),
        })?;
        let (parts, outputs) = plan(inputs, a, self.reference, root, laws, self.base, c)?
            .ok_or("対象族の元構成が未完成")?;
        let source = graph.get(self.reference)?;
        let (support, scope) = reading_metadata(inputs, a, source, c)?;
        if self.parts != parts
            || self.outputs != outputs
            || self.support != support
            || self.scope != scope
        {
            return Err("対象族が元対象・構成・Law・全計画・支持・scopeと違う".into());
        }
        tick(c)
    }
}
pub(super) fn retain(
    graph: &mut Graph,
    inputs: Arc<CheckedInputs>,
    reference: NodeRef,
    c: &mut Control,
) -> Result<Option<Diagram>, ValidationFailure> {
    tick(c)?;
    if graph.active != graph.context_at(reference.0) {
        return Err("対象族の生成が元ArchitectureのRequestでない".into());
    }
    let (a, root, laws) = origin(graph, reference)?;
    if inputs.sources() != Witness::Architecture(a.clone()).inputs().sources() {
        return Err("対象族の元三入力が違う".into());
    }
    let Some((parts, outputs)) = plan(&inputs, a, reference, root, laws, graph.nodes.len(), c)?
    else {
        return Ok(None);
    };
    let n = graph.get(reference)?;
    let (support, scope) = reading_metadata(&inputs, a, n, c)?;
    let source = Arc::new(Source {
        inputs,
        architecture: a.clone(),
        reference,
        root,
        laws: laws.to_vec(),
        base: graph.nodes.len(),
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
                data: D::ObjectComponents(data),
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
    let part = data
        .source
        .parts
        .get(data.index)
        .ok_or("対象族の元計画添字がない")?;
    let Some(Payload::Construction(v)) = &n.payload else {
        return Err("対象族のpayloadがない".into());
    };
    let Witness::Architecture(a) = &v.witness else {
        return Err("対象族の元由来がない".into());
    };
    let (original, root, laws) = origin(graph, data.source.reference)?;
    if !Arc::ptr_eq(a, original)
        || !Arc::ptr_eq(a, &data.source.architecture)
        || root != data.source.root
        || laws != data.source.laws
    {
        return Err("対象族の元Architecture参照が違う".into());
    }
    let (support, scope) = data.metadata();
    if n.ty != part.ty()
        || n.rule != Rule::Construction(part.construction())
        || n.arguments != data.arguments()
        || n.support != support
        || n.scope != scope
        || !n.reasons.is_empty()
        || !n.evidence.is_empty()
        || n.judgment.is_some()
    {
        return Err("対象族の型・辺・原始支持・scopeが違う".into());
    }
    for reference in part.arguments() {
        if reference == data.source.reference || reference == root || laws.contains(&reference) {
            graph.get(reference)?;
            continue;
        }
        let Some(Payload::Construction(v)) = &graph.get(reference)?.payload else {
            return Err("対象族の引数がnativeでない".into());
        };
        let D::ObjectComponents(other) = &v.data else {
            return Err("対象族の引数が別由来".into());
        };
        if !Arc::ptr_eq(&data.source, &other.source)
            || other.index >= data.index
            || data.source.base.checked_add(other.index) != Some(reference.0)
        {
            return Err("対象族の引数が元計画の既出値でない".into());
        }
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_object_components(
        &self,
        graph: &Graph,
        value: &ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        let D::ObjectComponents(data) = &value.data else {
            return Ok(());
        };
        tick(&mut self.control.clone())?;
        let Witness::Architecture(a) = &value.witness else {
            return Err("対象族のconsumerがArchitectureでない".into());
        };
        let (original, root, laws) = origin(graph, data.source.reference)?;
        if !Arc::ptr_eq(a, original)
            || !Arc::ptr_eq(a, &data.source.architecture)
            || root != data.source.root
            || laws != data.source.laws
        {
            return Err("対象族のconsumerが元Architectureと違う".into());
        }
        if self
            .verified_object_components
            .borrow()
            .iter()
            .any(|s| Arc::ptr_eq(s, &data.source))
        {
            return Ok(());
        }
        data.source
            .recheck(graph, self.inputs, a, &mut self.control.clone())?;
        self.verified_object_components
            .borrow_mut()
            .push(data.source.clone());
        Ok(())
    }
}
#[cfg(test)]
#[path = "object_component_diagram_tests.rs"]
mod tests;
