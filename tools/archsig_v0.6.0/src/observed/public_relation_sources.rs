//! 元relationの有限parameter域を、既存instance/Sourceの検査辺へ接続する。
use super::*;
use crate::observed::{
    call::Context,
    environment::relation_instances::{RelationInstances, RelationState},
};
use crate::{
    law::model::{Declaration, Signature},
    types::Type,
};
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct Family {
    pub table: RelationInstances,
}
impl std::fmt::Debug for Family {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RelationFamily")
            .field("declarations", &self.table.declarations.len())
            .field("instances", &self.table.instances.len())
            .finish()
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Template {
        declaration: usize,
        expression: usize,
        ty: Type,
        location: Location,
        parameters: Vec<(String, Type)>,
    },
    Parameter {
        instance: usize,
        parameter: usize,
        source: NodeRef,
        inputs: Vec<NodeRef>,
        value: Scalar,
    },
    Member {
        instance: usize,
        source: NodeRef,
        parameters: Vec<NodeRef>,
        value: Scalar,
    },
    Domain {
        declaration: usize,
        source: NodeRef,
        members: Vec<NodeRef>,
        ty: Type,
        finite: bool,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Data {
    pub kind: Kind,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
impl Data {
    pub fn scalar(&self) -> Option<&Scalar> {
        match &self.kind {
            Kind::Parameter { value, .. } | Kind::Member { value, .. } => Some(value),
            _ => None,
        }
    }
    pub fn ty(&self) -> NodeType {
        match &self.kind {
            Kind::Template { ty, .. } => NodeType::Expression(ty.clone()),
            Kind::Domain { .. } => NodeType::Domain,
            Kind::Parameter { value, .. } | Kind::Member { value, .. } => {
                NodeType::Value(value.ty())
            }
        }
    }
    pub fn construction(&self) -> &'static str {
        match self.kind {
            Kind::Template { .. } => "expression",
            _ => "domain",
        }
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        match &self.kind {
            Kind::Template { .. } => vec![],
            Kind::Parameter { source, inputs, .. } => std::iter::once(*source)
                .chain(inputs.iter().copied())
                .collect(),
            Kind::Member {
                source, parameters, ..
            } => std::iter::once(*source)
                .chain(parameters.iter().copied())
                .collect(),
            Kind::Domain {
                source, members, ..
            } => std::iter::once(*source)
                .chain(members.iter().copied())
                .collect(),
        }
    }
    pub fn wire(&self) -> Json {
        match &self.kind {
            Kind::Template {
                location,
                parameters,
                ..
            } => Json::obj([
                ("kind", Json::str("source")),
                ("location", crate::result::location_wire(location)),
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
                ("bindings", Json::Arr(vec![])),
            ]),
            Kind::Domain {
                ty, finite: false, ..
            } => Json::obj([("kind", Json::str("type")), ("type", ty.wire())]),
            Kind::Domain {
                ty,
                members,
                finite: true,
                ..
            } => Json::obj([
                ("kind", Json::str("finite")),
                ("type", ty.wire()),
                ("elements", refs(members)),
            ]),
            Kind::Parameter { value, .. } | Kind::Member { value, .. } => value.wire(),
        }
    }
}
fn family(w: &CompareWitness) -> Result<&Family, ValidationFailure> {
    w.relation_family
        .as_deref()
        .ok_or("relationの元instance族がない".into())
}
fn declaration(w: &CompareWitness, index: usize) -> Result<&Declaration, ValidationFailure> {
    family(w)?
        .table
        .declarations
        .get(index)
        .ok_or("元relation宣言の位置がない".into())
}
fn params(d: &Declaration) -> Result<&[crate::law::model::Param], ValidationFailure> {
    match &d.signature {
        Signature::Relation { params, .. } => Ok(params),
        _ => Err("元宣言がrelationでない".into()),
    }
}
fn owner_index(w: &CompareWitness, instance: usize) -> Result<usize, ValidationFailure> {
    let f = family(w)?;
    let row = f
        .table
        .instances
        .get(instance)
        .ok_or("元relation instanceがない")?;
    f.table
        .declarations
        .iter()
        .position(|d| d.name == row.declaration)
        .ok_or("instanceの元宣言がない".into())
}
pub(super) fn source_data<'a>(
    graph: &'a Graph,
    source: NodeRef,
    w: &CompareWitness,
) -> Result<&'a Data, ValidationFailure> {
    let value = value(graph, source)?;
    let Witness::Compare(original) = &value.witness else {
        return Err("relation Sourceの元検査が違う".into());
    };
    if original.request != w.request
        || original.inputs.sources() != w.inputs.sources()
        || original.relation_family != w.relation_family
    {
        return Err("relation Sourceの元入力・要求・族が違う".into());
    }
    match &value.data {
        D::Comparison(Part::RelationSource(data)) => Ok(data),
        _ => Err("relationの型付きSourceでない".into()),
    }
}
fn template(
    graph: &Graph,
    source: NodeRef,
    w: &CompareWitness,
    expected: usize,
) -> Result<(), ValidationFailure> {
    if !matches!(&source_data(graph,source,w)?.kind,Kind::Template{declaration,..} if *declaration==expected)
    {
        return Err("relationの元templateが違う".into());
    }
    Ok(())
}
fn caller(graph: &Graph, w: &CompareWitness) -> Result<Context, ValidationFailure> {
    if w.kind != "relation"
        || super::super::request::comparison::kind(&w.request)
            .map_err(|e| ValidationFailure::Internal(format!("relation kind: {e:?}")))?
            != "relation"
    {
        return Err("relationの元要求kindが違う".into());
    }
    let request = graph
        .requests
        .iter()
        .position(|r| r == &w.request)
        .ok_or("relationの元Requestがない")?;
    Ok(Context {
        request,
        ..Context::default()
    })
}
fn metadata(
    graph: &Graph,
    w: &CompareWitness,
    kind: &Kind,
) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
    let mut support = vec![];
    let mut scope = Scope::default();
    let args = match kind {
        Kind::Template {
            declaration: index, ..
        } => {
            scope
                .readings
                .insert(declaration(w, *index)?.reading.clone());
            vec![]
        }
        Kind::Parameter { source, inputs, .. } => std::iter::once(*source)
            .chain(inputs.iter().copied())
            .collect(),
        Kind::Member {
            source, parameters, ..
        } => std::iter::once(*source)
            .chain(parameters.iter().copied())
            .collect(),
        Kind::Domain {
            source, members, ..
        } => std::iter::once(*source)
            .chain(members.iter().copied())
            .collect(),
    };
    for r in args {
        let n = graph.get(r)?;
        support.extend(n.support.iter().cloned());
        scope.merge(&n.scope);
    }
    if let Kind::Domain {
        declaration: index, ..
    } = kind
    {
        for p in params(declaration(w, *index)?)? {
            scope.add_quantifier(Quantifier {
                kind: crate::law::ast::QuantKind::Forall,
                name: p.name.clone(),
                ty: p.ty.erase(),
                domain: None,
                occurrence: p.span,
                context: Some(caller(graph, w)?),
            });
        }
    }
    support.sort();
    support.dedup();
    Ok((support, scope))
}
pub(in crate::observed) fn validate_node(
    graph: &Graph,
    n: &Node,
    w: &CompareWitness,
    data: &Data,
) -> Result<(), ValidationFailure> {
    caller(graph, w)?;
    if !w.support.is_empty()
        || w.scope != Scope::default()
        || w.equal.is_some()
        || w.incompatible.is_some()
        || !w.facts.is_empty()
        || w.stopped.is_some()
        || w.value_plan.is_some()
        || w.relation_plan.is_some()
    {
        return Err("元relation Sourceの証人に比較結論を混入した".into());
    }
    let Scalar::Path(path) = graph.scalar(w.left)? else {
        return Err("元relation比較のPathがない".into());
    };
    if family(w)?.table.reading() != path.reading {
        return Err("relation族が比較operandのreadingと違う".into());
    }
    let (support, scope) = metadata(graph, w, &data.kind)?;
    if n.ty != data.ty()
        || n.rule != Rule::Construction(data.construction())
        || n.arguments != data.arguments()
        || data.support != support
        || data.scope != scope
        || n.support != support
        || n.scope != scope
        || n.judgment.is_some()
        || !n.evidence.is_empty()
        || !n.reasons.is_empty()
    {
        return Err("relation Sourceの型・辺・支持・Scopeが違う".into());
    }
    let f = family(w)?;
    match &data.kind {
        Kind::Template {
            declaration: index,
            expression,
            ty,
            location,
            parameters,
        } => {
            let d = declaration(w, *index)?;
            let Signature::Relation { params, left, .. } = &d.signature else {
                return Err("relation templateの署名が違う".into());
            };
            let law = w.inputs.law();
            if expression != left
                || law.expr_type(*left) != Some(ty)
                || location
                    != &(Location::Law {
                        span: law.exprs[*left].span,
                    })
                || parameters
                    != &params
                        .iter()
                        .map(|p| (p.name.clone(), p.ty.erase()))
                        .collect::<Vec<_>>()
            {
                return Err("relation templateが元式・parameterと違う".into());
            }
        }
        Kind::Parameter {
            instance,
            parameter,
            source,
            inputs,
            value: scalar,
        } => {
            let row = f.table.instances.get(*instance).ok_or("元instanceがない")?;
            let (_, expected) = row.bindings.get(*parameter).ok_or("元parameterがない")?;
            template(graph, *source, w, owner_index(w, *instance)?)?;
            if scalar != expected {
                return Err("relation parameterが元域のmemberでない".into());
            }
            for r in inputs {
                if !matches!(graph.scalar(*r)?, Scalar::Subject { .. }) {
                    return Err("parameterの参照支持が原始参照でない".into());
                }
            }
            let mut actual = vec![];
            let mut pending = vec![scalar];
            while let Some(v) = pending.pop() {
                match v {
                    Scalar::Subject { .. } => actual.push(v),
                    Scalar::Tuple(xs)
                    | Scalar::List { items: xs, .. }
                    | Scalar::Set { items: xs, .. }
                    | Scalar::Data { args: xs, .. } => pending.extend(xs),
                    Scalar::Map { pairs, .. } => {
                        for (a, b) in pairs {
                            pending.extend([a, b]);
                        }
                    }
                    Scalar::Option { value: Some(v), .. } => pending.push(v),
                    _ => {}
                }
            }
            let expected = actual
                .iter()
                .filter_map(|v| match v {
                    Scalar::Subject {
                        snapshot,
                        subject,
                        entity,
                    } => Some((snapshot.clone(), subject.clone(), entity.clone())),
                    _ => None,
                })
                .collect::<std::collections::BTreeSet<_>>();
            let actual = inputs
                .iter()
                .map(|r| match graph.scalar(*r)? {
                    Scalar::Subject {
                        snapshot,
                        subject,
                        entity,
                    } => Ok((snapshot.clone(), subject.clone(), entity.clone())),
                    _ => Err(ValidationFailure::Internal(
                        "parameterの原始参照が違う".into(),
                    )),
                })
                .collect::<Result<Vec<_>, _>>()?;
            if actual.len() != expected.len()
                || actual
                    .iter()
                    .cloned()
                    .collect::<std::collections::BTreeSet<_>>()
                    != expected
            {
                return Err("parameterの原始参照支持が完全な集合でない".into());
            }
        }
        Kind::Member {
            instance,
            source,
            parameters,
            value: scalar,
        } => {
            let row = f.table.instances.get(*instance).ok_or("元instanceがない")?;
            template(graph, *source, w, owner_index(w, *instance)?)?;
            if parameters.len() != row.bindings.len() {
                return Err("relation memberのparameter数が違う".into());
            }
            let values = parameters
                .iter()
                .map(|r| graph.scalar(*r).cloned())
                .collect::<Result<Vec<_>, _>>()?;
            if !values
                .iter()
                .zip(&row.bindings)
                .all(|(v, (_, expected))| v == expected)
            {
                return Err("relation memberの全束縛が元instanceと違う".into());
            }
            let expected = match values.as_slice() {
                [] => Scalar::Unit,
                [one] => one.clone(),
                _ => Scalar::Tuple(values),
            };
            if scalar != &expected {
                return Err("relation memberの元値が違う".into());
            }
        }
        Kind::Domain {
            declaration: index,
            source,
            members,
            ty,
            finite,
        } => {
            let d = declaration(w, *index)?;
            template(graph, *source, w, *index)?;
            if *finite != complete_domain(&f.table, &d.name) {
                return Err("relationの型域と完成した有限域を取り違えた".into());
            }
            let ps = params(d)?;
            let expected = match ps {
                [] => Type::Unit,
                [p] => p.ty.erase(),
                _ => Type::Tuple(ps.iter().map(|p| p.ty.erase()).collect()),
            };
            let rows = f
                .table
                .instances
                .iter()
                .enumerate()
                .filter(|(_, row)| row.declaration == d.name)
                .map(|(i, _)| i)
                .collect::<Vec<_>>();
            if ty != &expected || members.len() != rows.len() {
                return Err("relationの全instance域が元署名・全件数と違う".into());
            }
            for (r, index) in members.iter().zip(rows) {
                if !matches!(&source_data(graph,*r,w)?.kind,Kind::Member{instance,source:actual,..} if *instance==index && actual==source)
                {
                    return Err("relation域の元instance・順序が違う".into());
                }
            }
        }
    }
    Ok(())
}
fn source_witness(
    graph: &Graph,
    domain: NodeRef,
) -> Result<Option<(&CompareWitness, &Data)>, ValidationFailure> {
    let Some(Payload::Construction(value)) = &graph.get(domain)?.payload else {
        return Ok(None);
    };
    let (Witness::Compare(w), D::Comparison(Part::RelationSource(data))) =
        (&value.witness, &value.data)
    else {
        return Ok(None);
    };
    if matches!(data.kind, Kind::Domain { .. }) {
        Ok(Some((w, data)))
    } else {
        Ok(None)
    }
}
pub(in crate::observed) fn instance_declaration(
    graph: &Graph,
    index: usize,
) -> Result<Option<String>, ValidationFailure> {
    let record = graph
        .instances
        .get(index)
        .ok_or("relation instance索引がない")?;
    let Some((w, data)) = source_witness(graph, record.domain)? else {
        return Ok(None);
    };
    let Kind::Domain {
        declaration: index, ..
    } = data.kind
    else {
        return Ok(None);
    };
    Ok(Some(declaration(w, index)?.name.clone()))
}
pub(in crate::observed) struct InstanceBindings {
    pub bindings: Vec<Binding>,
    pub base: Scope,
}
pub(in crate::observed) fn instance_bindings(
    _env: &Environment<'_>,
    graph: &Graph,
    index: usize,
    limit: usize,
) -> Result<Option<InstanceBindings>, ValidationFailure> {
    let record = graph
        .instances
        .get(index)
        .ok_or("relation instance索引がない")?;
    let Some((w, data)) = source_witness(graph, record.domain)? else {
        return Ok(None);
    };
    if record.caller != caller(graph, w)?
        || [record.source, record.domain, record.member]
            .iter()
            .any(|r| r.0 >= limit)
        || graph.context_at(record.source.0) != record.caller
        || graph.context_at(record.domain.0) != record.caller
    {
        return Err("relation instanceの元Context・既出位置が違う".into());
    }
    let Kind::Domain {
        declaration: decl,
        source,
        members,
        ..
    } = &data.kind
    else {
        return Err("relation域がない".into());
    };
    if source != &record.source || !members.contains(&record.member) {
        return Err("relation instanceが元Domainのmemberでない".into());
    }
    let member = source_data(graph, record.member, w)?;
    let Kind::Member {
        instance,
        parameters,
        ..
    } = &member.kind
    else {
        return Err("relationの全束縛memberがない".into());
    };
    let row = family(w)?
        .table
        .instances
        .get(*instance)
        .ok_or("relation rowがない")?;
    if row.state == RelationState::OutsideDomain || row.declaration != declaration(w, *decl)?.name {
        return Err("relation rowが別宣言である".into());
    }
    let ps = params(declaration(w, *decl)?)?;
    let mut bindings = vec![];
    for (p, r) in ps.iter().zip(parameters) {
        if r.0 >= limit {
            return Err("relation parameterが未出である".into());
        }
        bindings.push(Binding {
            name: p.name.clone(),
            ty: p.ty.erase(),
            value: *r,
        });
    }
    Ok(Some(InstanceBindings {
        bindings,
        base: data.scope.clone(),
    }))
}

fn put_source(
    graph: &mut Graph,
    w: &Arc<CompareWitness>,
    kind: Kind,
) -> Result<NodeRef, ValidationFailure> {
    let (support, scope) = metadata(graph, w, &kind)?;
    node(
        graph,
        w,
        Part::RelationSource(Data {
            kind,
            support,
            scope,
        }),
        vec![],
        None,
    )
}
fn subject_value(
    env: &Environment<'_>,
    graph: &mut Graph,
    value: &Scalar,
) -> Result<NodeRef, ValidationFailure> {
    let Scalar::Subject {
        snapshot, subject, ..
    } = value
    else {
        return Err("元parameterが原始参照でない".into());
    };
    let node = subject_node(
        env,
        &Selector::Subject {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
        },
    )?;
    env.validate(graph, &node)?;
    graph.push(node)
}
fn parameter(
    env: &Environment<'_>,
    graph: &mut Graph,
    w: &Arc<CompareWitness>,
    instance: usize,
    index: usize,
    source: NodeRef,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteIteration)?;
    let scalar = family(w)?
        .table
        .instances
        .get(instance)
        .and_then(|row| row.bindings.get(index))
        .ok_or("元parameterがない")?
        .1
        .clone();
    if matches!(scalar, Scalar::Subject { .. }) {
        return subject_value(env, graph, &scalar);
    }
    let mut pending = vec![&scalar];
    let mut references = BTreeMap::<(String, String, String), Scalar>::new();
    while let Some(v) = pending.pop() {
        c.checkpoint(Checkpoint::FiniteIteration)?;
        match v {
            Scalar::Subject {
                snapshot,
                subject,
                entity,
            } => {
                references.insert(
                    (snapshot.clone(), subject.clone(), entity.clone()),
                    v.clone(),
                );
            }
            Scalar::Tuple(xs)
            | Scalar::List { items: xs, .. }
            | Scalar::Set { items: xs, .. }
            | Scalar::Data { args: xs, .. } => pending.extend(xs),
            Scalar::Map { pairs, .. } => {
                for (a, b) in pairs {
                    pending.extend([a, b]);
                }
            }
            Scalar::Option { value: Some(v), .. } => pending.push(v),
            _ => {}
        }
    }
    let inputs = references
        .values()
        .map(|v| subject_value(env, graph, v))
        .collect::<Result<Vec<_>, _>>()?;
    put_source(
        graph,
        w,
        Kind::Parameter {
            instance,
            parameter: index,
            source,
            inputs,
            value: scalar,
        },
    )
}
#[derive(Clone, Debug)]
pub(in crate::observed) struct Domains {
    pub sources: Vec<NodeRef>,
    pub domains: Vec<Option<NodeRef>>,
    pub instances: Vec<Option<usize>>,
}
pub(in crate::observed) fn domains(
    env: &Environment<'_>,
    graph: &mut Graph,
    w: &Arc<CompareWitness>,
    c: &mut Control,
) -> Result<Domains, ValidationFailure> {
    let f = family(w)?;
    let mut result = Domains {
        sources: vec![],
        domains: vec![],
        instances: vec![None; f.table.instances.len()],
    };
    let caller = caller(graph, w)?;
    if graph.active != caller {
        return Err("relation域の構成Contextが元要求と違う".into());
    }
    for (decl, d) in f.table.declarations.iter().enumerate() {
        c.checkpoint(Checkpoint::FiniteIteration)?;
        let Signature::Relation { params, left, .. } = &d.signature else {
            return Err("元relation署名がない".into());
        };
        let ty = w
            .inputs
            .law()
            .expr_type(*left)
            .ok_or("relation左式の元型がない")?
            .clone();
        let source = put_source(
            graph,
            w,
            Kind::Template {
                declaration: decl,
                expression: *left,
                ty,
                location: Location::Law {
                    span: w.inputs.law().exprs[*left].span,
                },
                parameters: params
                    .iter()
                    .map(|p| (p.name.clone(), p.ty.erase()))
                    .collect(),
            },
        )?;
        result.sources.push(source);
        let finite = complete_domain(&f.table, &d.name);
        // 全域を尽くしていなくても、得られた元束縛は型域のmemberとして
        // 再評価できる。有限全域の証拠は、完成した域にだけ付ける。
        if !finite
            && !f
                .table
                .instances
                .iter()
                .any(|row| row.declaration == d.name)
        {
            result.domains.push(None);
            continue;
        }
        let mut members = vec![];
        let mut row_indices = vec![];
        for (instance, row) in f
            .table
            .instances
            .iter()
            .enumerate()
            .filter(|(_, row)| row.declaration == d.name)
        {
            let mut parameters = vec![];
            for index in 0..row.bindings.len() {
                parameters.push(parameter(env, graph, w, instance, index, source, c)?);
            }
            let values = parameters
                .iter()
                .map(|r| graph.scalar(*r).cloned())
                .collect::<Result<Vec<_>, _>>()?;
            let value = match values.as_slice() {
                [] => Scalar::Unit,
                [v] => v.clone(),
                _ => Scalar::Tuple(values),
            };
            members.push(put_source(
                graph,
                w,
                Kind::Member {
                    instance,
                    source,
                    parameters,
                    value,
                },
            )?);
            row_indices.push(instance);
        }
        let ty = match params.as_slice() {
            [] => Type::Unit,
            [p] => p.ty.erase(),
            _ => Type::Tuple(params.iter().map(|p| p.ty.erase()).collect()),
        };
        let domain = put_source(
            graph,
            w,
            Kind::Domain {
                declaration: decl,
                source,
                members: members.clone(),
                ty,
                finite,
            },
        )?;
        result.domains.push(Some(domain));
        for (row, member) in row_indices.into_iter().zip(members) {
            c.checkpoint(Checkpoint::FiniteIteration)?;
            let index = graph.instances.len();
            graph.instances.push(crate::observed::call::Instance {
                caller,
                source,
                domain,
                member,
            });
            result.instances[row] = Some(index);
        }
    }
    Ok(result)
}

pub(super) fn complete_domain(table: &RelationInstances, declaration: &str) -> bool {
    // 検査済み表は全宣言を走査済み。別宣言の未完了域で、この宣言の
    // 完成した域と元反証を失わない。
    !table
        .outside_finite
        .iter()
        .any(|d| d.declaration == declaration)
        && !table
            .pending_domains
            .iter()
            .any(|d| d.declaration == declaration)
}
// guardが偽・未決の場合、元bodyを評価済みとして作らせない。
pub(in crate::observed) fn source_allowed(
    graph: &Graph,
    index: usize,
    span: (usize, usize),
) -> Result<bool, ValidationFailure> {
    let record = graph
        .instances
        .get(index)
        .ok_or("元relation instanceがない")?;
    let Some((w, _)) = source_witness(graph, record.domain)? else {
        return Ok(true);
    };
    let Kind::Member { instance, .. } = &source_data(graph, record.member, w)?.kind else {
        return Err("元relation memberがない".into());
    };
    let row = family(w)?
        .table
        .instances
        .get(*instance)
        .ok_or("元relation rowがない")?;
    let d = declaration(w, owner_index(w, *instance)?)?;
    if row.state == RelationState::OutsideDomain {
        return Ok(false);
    }
    if row.guard == Some(true) {
        return Ok(true);
    }
    let Signature::Relation {
        guard: Some(guard), ..
    } = &d.signature
    else {
        return Ok(false);
    };
    let outer = w.inputs.law().exprs[*guard].span;
    Ok(outer.0 <= span.0 && span.1 <= outer.1)
}
pub(in crate::observed) fn prepare_sources(
    prepared: &PreparedObserved,
    env: &Environment<'_>,
    graph: &mut Graph,
    request: &Request,
    left: NodeRef,
    right: NodeRef,
    control: &mut Control,
) -> Result<(Arc<CompareWitness>, Domains), ValidationFailure> {
    let Scalar::Path(path) = graph.scalar(left)? else {
        return Err("元relationのPathがない".into());
    };
    let table = super::super::environment::relation_instances::relation_instances(
        prepared.inputs(),
        &path.reading,
        control,
    )
    .map_err(|failure| failure.cause)?;
    let witness = Arc::new(CompareWitness {
        inputs: prepared.shared_inputs(),
        request: request.clone(),
        support: vec![],
        scope: Scope::default(),
        left,
        right,
        kind: "relation".into(),
        equal: None,
        incompatible: None,
        facts: vec![],
        stopped: None,
        value_plan: None,
        relation_family: Some(Arc::new(Family { table })),
        relation_plan: None,
    });
    let result = domains(env, graph, &witness, control)?;
    Ok((witness, result))
}
