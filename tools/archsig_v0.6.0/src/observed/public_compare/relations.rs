//! 元relationの有限な語閉包を、元AST評価と既存の証拠型へ接続する。
use super::*;
mod failures;
use crate::observed::{
    environment::relation_instances::{
        RelationState,
        congruence::{self, Congruence, QueryPath},
    },
    evaluate::{RelationSide, relation_side},
};
use crate::{law::model::Signature, types::Type};
#[derive(Clone, Debug, PartialEq, Eq)]
struct Row {
    original: usize,
    instance: usize,
    guard: Option<RelationSide>,
    left: Option<RelationSide>,
    right: Option<RelationSide>,
}
impl Row {
    fn references(&self) -> Vec<NodeRef> {
        self.guard
            .iter()
            .chain(self.left.iter())
            .chain(self.right.iter())
            .map(|side| side.evaluation)
            .collect()
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Data {
    FailureEvidence {
        left: NodeRef,
        right: NodeRef,
        facts: Vec<Fact>,
        arguments: Vec<NodeRef>,
    },
    FailureCondition {
        left: NodeRef,
        right: NodeRef,
        evidence: Vec<NodeRef>,
        arguments: Vec<NodeRef>,
    },
    // 語の有限証明書。原始参照の三つ組、順序列、閉包内の類を別の座標にする。
    Value {
        value: Scalar,
        arguments: Vec<NodeRef>,
    },
    Domain {
        ty: Type,
        elements: Vec<NodeRef>,
    },
    Rewrite {
        left: NodeRef,
        right: NodeRef,
        arguments: Vec<NodeRef>,
    },
    Exhaustion {
        domain: NodeRef,
        words: Vec<NodeRef>,
        steps: Vec<NodeRef>,
    },
    Normalization {
        before: NodeRef,
        after: NodeRef,
        steps: Vec<NodeRef>,
        closure: NodeRef,
    },
    Counterexample {
        left: NodeRef,
        right: NodeRef,
        closure: NodeRef,
        originals: [NodeRef; 2],
    },
}
impl Data {
    pub fn evidence(&self) -> Vec<NodeRef> {
        match self {
            Self::FailureCondition { evidence, .. } => evidence.clone(),
            _ => vec![],
        }
    }
    pub fn judgment(&self) -> Option<Judgment> {
        match self {
            Self::FailureCondition { evidence, .. } => Some(Judgment {
                status: Decision::Refuted,
                evidence: evidence.clone(),
                reasons: vec![],
            }),
            _ => None,
        }
    }
    pub fn scalar(&self) -> Option<&Scalar> {
        if let Self::Value { value, .. } = self {
            Some(value)
        } else {
            None
        }
    }
    pub fn ty(&self) -> NodeType {
        match self {
            Self::Value { value, .. } => NodeType::Value(value.ty()),
            Self::Domain { .. } => NodeType::Domain,
            Self::Rewrite { .. } => NodeType::Expression(Type::Bool),
            Self::FailureCondition { .. } => NodeType::Proposition,
            _ => NodeType::Evidence,
        }
    }
    pub fn construction(&self) -> &'static str {
        match self {
            Self::Value { .. } => "evaluation",
            Self::Domain { .. } => "domain",
            Self::Rewrite { .. } => "expression",
            Self::FailureCondition { .. } => "proposition",
            _ => "evidence",
        }
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Value { arguments, .. } => arguments.clone(),
            Self::FailureEvidence {
                left,
                right,
                arguments,
                ..
            }
            | Self::FailureCondition {
                left,
                right,
                arguments,
                ..
            } => [*left, *right]
                .into_iter()
                .chain(arguments.iter().copied())
                .collect(),
            Self::Domain { elements, .. } => elements.clone(),
            Self::Rewrite {
                left,
                right,
                arguments,
            } => std::iter::once(*left)
                .chain([*right])
                .chain(arguments.iter().copied())
                .collect(),
            Self::Exhaustion {
                domain,
                words,
                steps,
            } => std::iter::once(*domain)
                .chain(words.iter().copied())
                .chain(steps.iter().copied())
                .collect(),
            Self::Normalization {
                before,
                after,
                steps,
                closure,
            } => [*before, *after, *closure]
                .into_iter()
                .chain(steps.iter().copied())
                .collect(),
            Self::Counterexample {
                left,
                right,
                closure,
                originals,
            } => vec![*left, *right, *closure, originals[0], originals[1]],
        }
    }
    pub fn wire(&self) -> Json {
        match self {
            Self::FailureEvidence {
                left, right, facts, ..
            } => Json::obj([
                ("kind", Json::str("counterexample")),
                (
                    "data",
                    Json::obj([
                        ("bindings", Json::Arr(vec![])),
                        ("paths", Json::Arr(vec![])),
                        ("left", left.wire()),
                        ("right", right.wire()),
                        ("facts", Json::Arr(facts.iter().map(Fact::wire).collect())),
                    ]),
                ),
            ]),
            Self::FailureCondition { left, right, .. } => Json::obj([
                ("predicate", Json::str("equal")),
                ("operands", refs(&[*left, *right])),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            Self::Value { value, .. } => value.wire(),
            Self::Domain { ty, elements } => Json::obj([
                ("kind", Json::str("finite")),
                ("type", ty.wire()),
                ("elements", refs(elements)),
            ]),
            Self::Rewrite { left, right, .. } => Json::obj([
                ("kind", Json::str("transform")),
                ("operation", Json::str("equal")),
                ("operands", refs(&[*left, *right])),
                ("parameters", Json::Arr(vec![])),
                ("bindings", Json::Arr(vec![])),
            ]),
            Self::Exhaustion { domain, words, .. } => Json::obj([
                ("kind", Json::str("finite_exhaustion")),
                (
                    "data",
                    Json::obj([
                        ("domain", domain.wire()),
                        ("checked", Json::Nat(words.len() as u64)),
                        ("instances", refs(words)),
                    ]),
                ),
            ]),
            Self::Normalization {
                before,
                after,
                steps,
                ..
            } => Json::obj([
                ("kind", Json::str("normalization")),
                (
                    "data",
                    Json::obj([
                        ("before", before.wire()),
                        ("after", after.wire()),
                        ("steps", refs(steps)),
                    ]),
                ),
            ]),
            Self::Counterexample { left, right, .. } => Json::obj([
                ("kind", Json::str("counterexample")),
                (
                    "data",
                    Json::obj([
                        ("bindings", Json::Arr(vec![])),
                        ("paths", Json::Arr(vec![])),
                        ("left", left.wire()),
                        ("right", right.wire()),
                        ("facts", Json::Arr(vec![])),
                    ]),
                ),
            ]),
        }
    }
}
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct Plan {
    pub base: usize,
    context: crate::observed::call::Context,
    base_scope: Scope,
    pub nodes: Vec<Data>,
    model: Congruence,
    rows: Vec<Row>,
    source_refs: Vec<NodeRef>,
    domain_refs: Vec<Option<NodeRef>>,
    references: BTreeMap<(String, String, String), NodeRef>,
    pub(in crate::observed) dependencies: Vec<NodeRef>,
    pub equal: Option<bool>,
    condition: Option<NodeRef>,
    pub evidence: Vec<NodeRef>,
    pub reasons: Vec<Reason>,
}
impl std::fmt::Debug for Plan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RelationComparison")
            .field("words", &self.model.words.len())
            .field("nodes", &self.nodes.len())
            .finish()
    }
}
fn triple(value: &(String, String, String)) -> Scalar {
    Scalar::Tuple(vec![
        Scalar::Text(value.0.clone()),
        Scalar::Text(value.1.clone()),
        Scalar::Text(value.2.clone()),
    ])
}
fn triple_type() -> Type {
    Type::Tuple(vec![Type::Text, Type::Text, Type::Text])
}
fn certificate_type() -> Type {
    Type::Tuple(vec![
        triple_type(),
        triple_type(),
        Type::List(Box::new(triple_type())),
        Type::Z,
    ])
}
fn certificate(model: &Congruence, index: usize) -> Result<Scalar, ValidationFailure> {
    let word = model.words.get(index).ok_or("閉包の元語がない")?;
    let class = *model.classes.get(index).ok_or("閉包の元類がない")?;
    Ok(Scalar::Tuple(vec![
        triple(&word.source),
        triple(&word.target),
        Scalar::List {
            element: triple_type(),
            items: word.generators.iter().map(triple).collect(),
        },
        Scalar::Z(class.into()),
    ]))
}
// Consume the checked Operation itself; retain its word and actual total action.
pub(super) fn operand_path(
    graph: &Graph,
    reference: NodeRef,
) -> Result<crate::observed::path_value::PathValue, ValidationFailure> {
    if let Ok(Scalar::Path(path)) = graph.scalar(reference) {
        return Ok(path.as_ref().clone());
    }
    let operation = crate::observed::public_compose::op(graph, reference)?;
    let inputs = value(graph, reference)?.witness.inputs();
    let scalar = |fact: &crate::archmap::Fact| -> Result<Scalar, ValidationFailure> {
        let subject = inputs
            .archmap()
            .snapshots
            .iter()
            .flat_map(|s| &s.subjects)
            .find(|s| s.snapshot == fact.snapshot && s.id == fact.subject)
            .ok_or("操作の元subjectがない")?;
        Ok(Scalar::Subject {
            snapshot: fact.snapshot.clone(),
            subject: fact.subject.clone(),
            entity: subject.ty.clone(),
        })
    };
    let fact = |p: &crate::archmap::Fact| Fact {
        snapshot: p.snapshot.clone(),
        subject: p.subject.clone(),
        field: p.field.clone(),
        atom: p.atom.clone(),
    };
    let source = operation.source();
    let target = operation.target();
    let root = scalar(source.subject())?;
    let Scalar::Subject {
        snapshot,
        subject,
        entity,
    } = &root
    else {
        return Err("操作のsourceが原始参照でない".into());
    };
    let generators = operation
        .word()
        .iter()
        .map(scalar)
        .collect::<Result<Vec<_>, _>>()?;
    let mut action = operation
        .map()
        .candidate()
        .universe()
        .iter()
        .zip(operation.map().candidate().images())
        .map(|(from, to)| (fact(from), fact(to)))
        .collect::<Vec<_>>();
    action.sort_by(|a, b| a.0.cmp(&b.0));
    let (carrier, images) = action.into_iter().unzip();
    let step = if let Some(generator) = generators.first() {
        Some(Box::new(crate::observed::path_value::Step {
            generator: generator.clone(),
            word_tail: generators[1..].to_vec(),
            target: scalar(target.subject())?,
            carrier,
            images,
        }))
    } else {
        None
    };
    Ok(crate::observed::path_value::PathValue {
        reading: source.reading().into(),
        snapshot: snapshot.clone(),
        subject: subject.clone(),
        entity: entity.clone(),
        step,
    })
}

fn queries(
    graph: &Graph,
    left: NodeRef,
    right: NodeRef,
) -> Result<Vec<QueryPath>, ValidationFailure> {
    [left, right]
        .into_iter()
        .map(|r| {
            let node = graph.get(r)?;
            let path = operand_path(graph, r)?;
            Ok(QueryPath {
                path,
                support: node.support.clone(),
                scope: node.scope.clone(),
            })
        })
        .collect()
}
fn put_data(nodes: &mut Vec<Data>, base: usize, data: Data) -> NodeRef {
    let r = NodeRef(base + nodes.len());
    nodes.push(data);
    r
}
fn build_nodes(
    graph: &Graph,
    model: &Congruence,
    rows: &[Row],
    references: &BTreeMap<(String, String, String), NodeRef>,
    dependencies: &[NodeRef],
    base: usize,
    left: NodeRef,
    right: NodeRef,
    c: &mut Control,
) -> Result<(Vec<Data>, Vec<NodeRef>), ValidationFailure> {
    if !model.complete() {
        return Ok((vec![], vec![]));
    }
    let mut nodes = vec![];
    let mut words = vec![];
    for (index, word) in model.words.iter().enumerate() {
        c.checkpoint(Checkpoint::FiniteIteration)?;
        let mut arguments = dependencies.to_vec();
        for name in std::iter::once(&word.source)
            .chain([&word.target])
            .chain(&word.generators)
        {
            let r = *references.get(name).ok_or("語の原始参照がない")?;
            let expected = Scalar::Subject {
                snapshot: name.0.clone(),
                subject: name.1.clone(),
                entity: name.2.clone(),
            };
            if graph.scalar(r)? != &expected {
                return Err("語の名前が現在の原始参照と違う".into());
            }
            arguments.push(r);
        }
        words.push(put_data(
            &mut nodes,
            base,
            Data::Value {
                value: certificate(model, index)?,
                arguments,
            },
        ));
    }
    let mut steps = vec![];
    for edge in &model.edges {
        c.checkpoint(Checkpoint::FiniteIteration)?;
        let row = rows
            .iter()
            .find(|row| row.original == edge.instance)
            .ok_or("書換えの元relation rowがない")?;
        let left_side = row.left.as_ref().ok_or("書換えの左元評価がない")?;
        let right_side = row.right.as_ref().ok_or("書換えの右元評価がない")?;
        let (a, b) = if edge.right_to_left {
            (right_side, left_side)
        } else {
            (left_side, right_side)
        };
        let direction = put_data(
            &mut nodes,
            base,
            Data::Value {
                value: Scalar::Tuple(vec![
                    Scalar::Bool(edge.right_to_left),
                    Scalar::Z(edge.offset.into()),
                ]),
                arguments: row.references(),
            },
        );
        let mut arguments = row.references();
        arguments.extend([words[edge.from], words[edge.to], direction]);
        steps.push(put_data(
            &mut nodes,
            base,
            Data::Rewrite {
                left: a.value.ok_or("書換えの左値がない")?,
                right: b.value.ok_or("書換えの右値がない")?,
                arguments,
            },
        ));
    }
    let domain = put_data(
        &mut nodes,
        base,
        Data::Domain {
            ty: certificate_type(),
            elements: words.clone(),
        },
    );
    let closure = put_data(
        &mut nodes,
        base,
        Data::Exhaustion {
            domain,
            words: words.clone(),
            steps: steps.clone(),
        },
    );
    let a = *model.query_ids.first().ok_or("左queryの語がない")?;
    let b = *model.query_ids.get(1).ok_or("右queryの語がない")?;
    let equal = model
        .equivalent(a, b, c)?
        .ok_or("未完成の閉包を証拠にした")?;
    let evidence = if equal {
        let proof = model.derivation(a, b, c)?.ok_or("同値導出がない")?;
        let mut expressions = vec![];
        for step in proof {
            c.checkpoint(Checkpoint::FiniteIteration)?;
            // 逆向きの適用は両辺・文脈・方向を反転し、元の順向き証拠も保持する。
            if step.backwards {
                let Data::Rewrite { left, right, .. } = nodes[steps[step.edge].0 - base].clone()
                else {
                    return Err("元書換え式がない".into());
                };
                let edge = model.edges.get(step.edge).ok_or("逆適用の元edgeがない")?;
                let row = rows
                    .iter()
                    .find(|row| row.original == edge.instance)
                    .ok_or("逆適用の元relation rowがない")?;
                let direction = put_data(
                    &mut nodes,
                    base,
                    Data::Value {
                        value: Scalar::Tuple(vec![
                            Scalar::Bool(!edge.right_to_left),
                            Scalar::Z(edge.offset.into()),
                        ]),
                        arguments: row.references(),
                    },
                );
                let mut arguments = row.references();
                arguments.extend([
                    words[edge.to],
                    words[edge.from],
                    direction,
                    steps[step.edge],
                ]);
                expressions.push(put_data(
                    &mut nodes,
                    base,
                    Data::Rewrite {
                        left: right,
                        right: left,
                        arguments,
                    },
                ));
            } else {
                expressions.push(steps[step.edge]);
            }
        }
        put_data(
            &mut nodes,
            base,
            Data::Normalization {
                before: left,
                after: right,
                steps: expressions,
                closure,
            },
        )
    } else {
        put_data(
            &mut nodes,
            base,
            Data::Counterexample {
                left: words[a],
                right: words[b],
                closure,
                originals: [left, right],
            },
        )
    };
    Ok((nodes, vec![closure, evidence]))
}
pub(in crate::observed) fn evaluate(
    prepared: &PreparedObserved,
    env: &Environment<'_>,
    graph: &mut Graph,
    request: &Request,
    left: NodeRef,
    right: NodeRef,
    c: &mut Control,
) -> Result<Answer, ValidationFailure> {
    let operands = queries(graph, left, right)?;
    if operands[0].path.reading != operands[1].path.reading
        || operands[0].path.object() != operands[1].path.object()
        || operands[0].path.target() != operands[1].path.target()
    {
        return Err("relation比較の実端点・readingが違う".into());
    }
    let (source, domains) =
        relation_sources::prepare_sources(prepared, env, graph, request, left, right, c)?;
    let table = &source
        .relation_family
        .as_ref()
        .ok_or("元relation族がない")?
        .table;
    let mut rows = vec![];
    let mut dependencies = domains.sources.clone();
    dependencies.extend(domains.domains.iter().flatten().copied());
    dependencies.extend([left, right]);
    for (original, row) in table.instances.iter().enumerate() {
        c.checkpoint(Checkpoint::FiniteIteration)?;
        let Some(instance) = domains.instances[original] else {
            continue;
        };
        if row.state == RelationState::OutsideDomain {
            continue;
        }
        let declaration = table
            .declarations
            .iter()
            .find(|d| d.name == row.declaration)
            .ok_or("元relation宣言がない")?;
        let Signature::Relation {
            guard,
            left: le,
            right: re,
            ..
        } = declaration.signature
        else {
            return Err("元relation署名が違う".into());
        };
        let mut visible = Row {
            original,
            instance,
            guard: None,
            left: None,
            right: None,
        };
        if let Some(g) = guard {
            visible.guard = Some(relation_side(
                env,
                graph,
                c,
                request,
                declaration,
                instance,
                g,
            )?);
        }
        if row.guard == Some(true) {
            visible.left = Some(relation_side(
                env,
                graph,
                c,
                request,
                declaration,
                instance,
                le,
            )?);
            visible.right = Some(relation_side(
                env,
                graph,
                c,
                request,
                declaration,
                instance,
                re,
            )?);
        }
        dependencies.extend(visible.references());
        rows.push(visible);
    }
    let model =
        congruence::with_queries(prepared.inputs(), &operands[0].path.reading, &operands, c)
            .map_err(|f| f.cause)?;
    let invalid = table.instances.iter().any(|row| {
        matches!(
            row.state,
            RelationState::Refuted | RelationState::ConditionFailed
        )
    });
    if !invalid && (!model.unbalanced.is_empty() || !table.outside_finite.is_empty()) {
        let (name, detail) = if let Some(parameter) = table.outside_finite.first() {
            (
                &parameter.declaration,
                format!(
                    "parameter {}: {} の有限列挙以外の算法",
                    parameter.parameter,
                    parameter.ty.wire().canonical()
                ),
            )
        } else {
            let index = *model
                .unbalanced
                .first()
                .ok_or("長さ変更の元instanceがない")?;
            let row = table
                .instances
                .get(index)
                .ok_or("長さ変更の元relationがない")?;
            (&row.declaration, "語長を変える関係の算法".into())
        };
        let declaration = table
            .declarations
            .iter()
            .find(|declaration| &declaration.name == name)
            .ok_or("未実装算法の元relation宣言がない")?;
        c.checkpoint(Checkpoint::FiniteIteration)?;
        return Err(ValidationFailure::UnsupportedExpression {
            location: Location::Law {
                span: declaration.span,
            },
            feature: format!("relation {name}: {detail}は未実装"),
        });
    }
    let mut references = BTreeMap::new();
    for word in model.words.iter().filter(|_| model.complete()) {
        for name in std::iter::once(&word.source)
            .chain([&word.target])
            .chain(&word.generators)
        {
            if references.contains_key(name) {
                continue;
            }
            let n = subject_node(
                env,
                &Selector::Subject {
                    snapshot: name.0.clone(),
                    subject: name.1.clone(),
                },
            )?;
            env.validate(graph, &n)?;
            let r = graph.push(n)?;
            references.insert(name.clone(), r);
        }
    }
    let base = graph.nodes.len();
    let calculated = failures::calculate(
        graph,
        &model,
        &rows,
        &references,
        &dependencies,
        &domains.sources,
        base,
        left,
        right,
        request,
        c,
    )?;
    let equal = model.equivalent(model.query_ids[0], model.query_ids[1], c)?;
    let (support, base_scope) = proof_metadata(graph, &model, &dependencies)?;
    c.checkpoint(Checkpoint::FiniteIteration)?;
    let plan = Arc::new(Plan {
        base,
        context: graph.active,
        base_scope,
        nodes: calculated.nodes,
        condition: calculated.condition,
        model,
        reasons: calculated.reasons,
        rows,
        source_refs: domains.sources,
        domain_refs: domains.domains,
        references,
        dependencies,
        equal,
        evidence: calculated.evidence,
    });
    let evidence = plan.evidence.clone();
    let scope = scope_at(&plan, None);
    let witness = Arc::new(CompareWitness {
        inputs: prepared.shared_inputs(),
        request: request.clone(),
        support,
        scope: scope.clone(),
        left,
        right,
        kind: "relation".into(),
        equal,
        incompatible: None,
        facts: vec![],
        stopped: None,
        value_plan: None,
        relation_family: source.relation_family.clone(),
        relation_plan: Some(plan.clone()),
    });
    for (index, data) in plan.nodes.iter().enumerate() {
        let r = node(
            graph,
            &witness,
            Part::RelationDerived {
                index,
                data: Box::new(data.clone()),
            },
            data.evidence(),
            data.judgment(),
        )?;
        if r.0 != base + index {
            return Err("元relation証拠の転記位置が違う".into());
        }
    }
    let comparison = if plan.condition.is_none() {
        Some(node(
            graph,
            &witness,
            Part::Comparison {
                kind: "relation".into(),
                left,
                right,
            },
            vec![],
            None,
        )?)
    } else {
        None
    };
    let name = if plan.condition.is_some() {
        Some(put(
            graph,
            &witness,
            D::ConstructionLabel(Scalar::Text("comparison".into())),
            vec![],
            None,
        )?)
    } else {
        None
    };
    let status = decision(equal, plan.condition);
    let claim = node(
        graph,
        &witness,
        Part::Claim {
            left,
            right,
            comparison,
            name,
            condition: plan.condition,
        },
        evidence.clone(),
        Some(Judgment {
            status,
            evidence: evidence.clone(),
            reasons: plan.reasons.clone(),
        }),
    )?;
    Ok(Answer {
        id: request.id.clone(),
        status,
        outputs: std::iter::once(("proposition".into(), claim))
            .chain(comparison.map(|r| ("comparison".into(), r)))
            .collect(),
        claim: Some(claim),
        evidence,
        reasons: plan.reasons.clone(),
        scope,
    })
}
pub(in crate::observed) fn recheck(
    graph: &Graph,
    w: &CompareWitness,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let plan = w
        .relation_plan
        .as_ref()
        .ok_or("元relationの計算証拠がない")?;
    if w.kind != "relation"
        || w.value_plan.is_some()
        || w.incompatible.is_some()
        || !w.facts.is_empty()
        || w.stopped.is_some()
    {
        return Err("relationの比較条件が違う".into());
    }
    let operands = queries(graph, w.left, w.right)?;
    plan.model
        .recheck_queries(&w.inputs, &operands, c)
        .map_err(|f| f.cause)?;
    let table = plan.model.relations.as_ref().ok_or("元relation表がない")?;
    let (support, base_scope) = proof_metadata(graph, &plan.model, &plan.dependencies)?;
    if w.relation_family.as_ref().map(|f| &f.table) != Some(table)
        || w.support != support
        || plan.base_scope != base_scope
        || w.scope != scope_at(plan, None)
        || graph.requests.get(plan.context.request) != Some(&w.request)
        || plan.context
            != (crate::observed::call::Context {
                request: plan.context.request,
                ..crate::observed::call::Context::default()
            })
    {
        return Err("元relationの族・支持・範囲が違う".into());
    }
    let count = table.declarations.len();
    if plan.source_refs.len() != count || plan.domain_refs.len() != count {
        return Err("元relationの域件数が違う".into());
    }
    let mut dependencies = plan.source_refs.clone();
    for index in 0..count {
        let r = plan.source_refs[index];
        if !matches!(&relation_sources::source_data(graph,r,w)?.kind,relation_sources::Kind::Template{declaration,..} if *declaration==index)
        {
            return Err("元relation templateの順序が違う".into());
        }
        let complete = relation_sources::complete_domain(table, &table.declarations[index].name);
        let available = complete
            || table
                .instances
                .iter()
                .any(|row| row.declaration == table.declarations[index].name);
        match plan.domain_refs[index] {
            Some(r) if available => {
                if !matches!(&relation_sources::source_data(graph,r,w)?.kind,relation_sources::Kind::Domain{declaration,source,finite,..} if *declaration==index && *source==plan.source_refs[index] && *finite==complete)
                {
                    return Err("元relation全域の順序が違う".into());
                }
                dependencies.push(r);
            }
            None if !available => {}
            _ => return Err("元relation域の完成状態が違う".into()),
        }
    }
    dependencies.extend([w.left, w.right]);
    let originals = table
        .instances
        .iter()
        .enumerate()
        .filter(|(_, r)| r.state != RelationState::OutsideDomain)
        .collect::<Vec<_>>();
    if plan.rows.len() != originals.len() {
        return Err("元relationの全rowが保持されていない".into());
    }
    for (visible, (index, row)) in plan.rows.iter().zip(originals) {
        c.checkpoint(Checkpoint::FiniteIteration)?;
        if visible.original != index {
            return Err("元relation rowの順序が違う".into());
        }
        let record = graph
            .instances
            .get(visible.instance)
            .ok_or("元relation frameがない")?;
        if !matches!(&relation_sources::source_data(graph,record.member,w)?.kind,relation_sources::Kind::Member{instance,..} if *instance==index)
        {
            return Err("元relation rowが別instanceを指す".into());
        }
        let declaration = table
            .declarations
            .iter()
            .find(|d| d.name == row.declaration)
            .ok_or("元relation宣言がない")?;
        let Signature::Relation {
            guard, left, right, ..
        } = declaration.signature
        else {
            return Err("元relation署名がない".into());
        };
        if visible.guard.is_some() != guard.is_some()
            || visible.left.is_some() != (row.guard == Some(true))
            || visible.right.is_some() != (row.guard == Some(true))
        {
            return Err("元guardの適用範囲が違う".into());
        }
        for (side, expression, expected) in [
            (visible.guard.as_ref(), guard, row.guard.map(Scalar::Bool)),
            (visible.left.as_ref(), Some(left), row.left.clone()),
            (visible.right.as_ref(), Some(right), row.right.clone()),
        ] {
            let Some(side) = side else {
                continue;
            };
            let node = graph.get(side.evaluation)?;
            let Some(Payload::Evaluation {
                expression: actual,
                bindings,
                value,
                ..
            }) = &node.payload
            else {
                return Err("元relationの評価がない".into());
            };
            if side.evaluation.0 >= plan.base
                || side.expression != *actual
                || side.value != *value
                || side.scope != node.scope
                || side.support != node.support
                || side.reasons != node.reasons
                || graph.context_at(side.evaluation.0).instance != Some(visible.instance)
                || graph.context_at(side.evaluation.0).frame.is_some()
                || graph.context_at(side.evaluation.0).iteration.is_some()
                || bindings.len() != row.bindings.len()
            {
                return Err("元relation評価のContext・値・範囲が違う".into());
            }
            let Some(Payload::Expression {
                location: Location::Law { span },
                bindings: source_bindings,
                parameters,
            }) = &graph.get(*actual)?.payload
            else {
                return Err("元relationのSourceがない".into());
            };
            let expression = expression.ok_or("元relationの式がない")?;
            if *span != w.inputs.law().exprs[expression].span
                || source_bindings != bindings
                || !parameters.is_empty()
            {
                return Err("元relationのAST出現が違う".into());
            }
            for (binding, (name, expected)) in bindings.iter().zip(&row.bindings) {
                if &binding.name != name || graph.scalar(binding.value)? != expected {
                    return Err("元relationの束縛が違う".into());
                }
            }
            let actual = value.map(|r| graph.scalar(r).cloned()).transpose()?;
            if actual != expected {
                return Err("元relationの実評価値が違う".into());
            }
        }
        dependencies.extend(visible.references());
    }
    if dependencies != plan.dependencies
        || dependencies.iter().any(|r| r.0 >= plan.base)
        || plan.references.values().any(|r| r.0 >= plan.base)
    {
        return Err("元relation依存の全件・既出位置が違う".into());
    }
    let expected_names = plan
        .model
        .words
        .iter()
        .filter(|_| plan.model.complete())
        .flat_map(|word| {
            std::iter::once(&word.source)
                .chain([&word.target])
                .chain(&word.generators)
        })
        .cloned()
        .collect::<std::collections::BTreeSet<_>>();
    if plan
        .references
        .keys()
        .cloned()
        .collect::<std::collections::BTreeSet<_>>()
        != expected_names
    {
        return Err("合同語の原始参照集合が違う".into());
    }
    for reference in plan.references.values() {
        if graph.context_at(reference.0) != plan.context
            || !matches!(
                graph.get(*reference)?.rule,
                Rule::Input {
                    kind: "subject",
                    ..
                }
            )
        {
            return Err("合同語の原始参照の生成Contextが違う".into());
        }
    }
    let last = plan
        .dependencies
        .iter()
        .chain(plan.references.values())
        .map(|r| r.0)
        .max()
        .ok_or("relationの元依存がない")?;
    if last.checked_add(1) != Some(plan.base) {
        return Err("relation証拠の開始位置が元prefix末尾と違う".into());
    }
    let calculated = failures::calculate(
        graph,
        &plan.model,
        &plan.rows,
        &plan.references,
        &dependencies,
        &plan.source_refs,
        plan.base,
        w.left,
        w.right,
        &w.request,
        c,
    )?;
    let equal = plan
        .model
        .equivalent(plan.model.query_ids[0], plan.model.query_ids[1], c)?;
    if calculated.nodes != plan.nodes
        || calculated.evidence != plan.evidence
        || calculated.condition != plan.condition
        || equal != plan.equal
        || w.equal != equal
        || plan.reasons != calculated.reasons
    {
        return Err("relationの閉包・導出・判断が再計算と違う".into());
    }
    Ok(())
}
pub(in crate::observed) fn validate_node(
    graph: &Graph,
    n: &Node,
    w: &CompareWitness,
) -> Result<(), ValidationFailure> {
    let plan = w.relation_plan.as_ref().ok_or("relationの元計算がない")?;
    let Some(Payload::Construction(v)) = &n.payload else {
        return Err("relationのpayloadがない".into());
    };
    if n.ty != v.ty()
        || n.rule != v.rule()
        || n.arguments != v.arguments()
        || n.support != w.support
        || n.scope
            != match &v.data {
                D::Comparison(Part::RelationDerived { index, .. }) => {
                    scope_at(plan, Some(plan.base + index))
                }
                _ => w.scope.clone(),
            }
        || !n.reasons.is_empty()
    {
        return Err("relationの型・規則・元辺・支持・Scopeが違う".into());
    }
    match &v.data {
        D::Comparison(Part::RelationDerived { index, data }) => {
            if plan.nodes.get(*index) != Some(data.as_ref())
                || n.judgment != data.judgment()
                || n.evidence != data.evidence()
            {
                return Err("relationの元証拠が違う".into());
            }
        }
        D::Comparison(Part::Comparison { kind, left, right }) => {
            if plan.condition.is_some()
                || kind != "relation"
                || (*left, *right) != (w.left, w.right)
                || n.judgment.is_some()
                || !n.evidence.is_empty()
            {
                return Err("relationのComparisonが違う".into());
            }
        }
        D::Comparison(Part::Claim {
            left,
            right,
            comparison,
            name,
            condition,
        }) => {
            let shape = match (plan.condition, comparison, name, condition) {
                (None, Some(comparison), None, None) => {
                    matches!(part(graph, *comparison, w)?, Part::Comparison { .. })
                }
                (Some(expected), None, Some(name), Some(actual)) if expected == *actual => {
                    let label = value(graph, *name)?;
                    matches!(&label.witness,Witness::Compare(original) if original.as_ref()==w)
                        && label.scalar() == Some(&Scalar::Text("comparison".into()))
                }
                _ => false,
            };
            if !shape
                || (*left, *right) != (w.left, w.right)
                || n.evidence != plan.evidence
                || n.judgment
                    != Some(Judgment {
                        status: decision(plan.equal, plan.condition),
                        evidence: plan.evidence.clone(),
                        reasons: plan.reasons.clone(),
                    })
            {
                return Err("relationの命題・判断・証拠が違う".into());
            }
        }
        D::ConstructionLabel(Scalar::Text(label))
            if plan.condition.is_some()
                && label == "comparison"
                && n.judgment.is_none()
                && n.evidence.is_empty() => {}
        _ => return Err("relationに別の構成を混ぜた".into()),
    }
    Ok(())
}

pub(in crate::observed) fn scope_at(plan: &Plan, position: Option<usize>) -> Scope {
    let mut scope = plan.base_scope.clone();
    if let Some(index) = plan
        .nodes
        .iter()
        .position(|data| matches!(data, Data::Domain { .. }))
    {
        let domain = NodeRef(plan.base + index);
        if position.is_none_or(|position| position > domain.0) {
            scope.add_quantifier(Quantifier {
                kind: crate::law::ast::QuantKind::Forall,
                name: "relation_word".into(),
                ty: certificate_type(),
                domain: Some(domain),
                occurrence: (0, 0),
                context: Some(plan.context),
            });
        }
    }
    scope
}

fn decision(equal: Option<bool>, condition: Option<NodeRef>) -> Decision {
    if condition.is_some() {
        return Decision::Refuted;
    }
    match equal {
        Some(true) => Decision::Established,
        Some(false) => Decision::Refuted,
        None => Decision::Undetermined,
    }
}
fn missing_reasons(
    table: &crate::observed::environment::relation_instances::RelationInstances,
    rows: &[Row],
    sources: &[NodeRef],
    request: &Request,
) -> Result<Vec<Reason>, ValidationFailure> {
    let mut reasons = vec![];
    for row in rows {
        for side in row
            .guard
            .iter()
            .chain(row.left.iter())
            .chain(row.right.iter())
        {
            reasons.extend(side.reasons.clone());
        }
    }
    for pending in &table.pending_domains {
        let index = table
            .declarations
            .iter()
            .position(|d| d.name == pending.declaration)
            .ok_or("欠測域の元relation宣言がない")?;
        let Signature::Relation { params, .. } = &table.declarations[index].signature else {
            return Err("欠測域の元署名が違う".into());
        };
        let parameter = params
            .iter()
            .find(|p| p.name == pending.parameter)
            .ok_or("欠測域の元parameterがない")?;
        reasons.push(Reason {
            kind: ReasonKind::Missing,
            request: request.id.clone(),
            dependencies: vec![*sources.get(index).ok_or("欠測域の元Sourceがない")?],
            missing: pending.missing.clone(),
            location: Some(Location::Law {
                span: parameter.span,
            }),
        });
    }
    sort_reasons(&mut reasons);
    Ok(reasons)
}

pub(in crate::observed) fn validate_failure(
    graph: &Graph,
    reason: &Reason,
    condition: NodeRef,
    w: &CompareWitness,
) -> Result<(), ValidationFailure> {
    if reason != &failed(&w.request, condition)
        || !matches!(part(graph,condition,w)?,Part::RelationDerived{data,..} if matches!(data.as_ref(),Data::FailureCondition{..}))
    {
        return Err("元relation反証の構成失敗理由が違う".into());
    }
    validate_node(graph, graph.get(condition)?, w)
}

pub(in crate::observed) fn validate_incompatible(
    graph: &Graph,
    w: &CompareWitness,
) -> Result<(), ValidationFailure> {
    let (x, y) = w.incompatible.ok_or("relationの元不適合条件がない")?;
    if w.equal.is_some()
        || w.value_plan.is_some()
        || !w.facts.is_empty()
        || w.stopped.is_some()
        || crate::observed::request::comparison::kind(&w.request)
            .map_err(|e| ValidationFailure::Internal(format!("比較kind: {e:?}")))?
            != "relation"
    {
        return Err("relationの不適合条件が変わった".into());
    }
    let mut support = graph.get(w.left)?.support.clone();
    support.extend(graph.get(w.right)?.support.iter().cloned());
    support.sort();
    support.dedup();
    let mut scope = graph.get(w.left)?.scope.clone();
    scope.merge(&graph.get(w.right)?.scope);
    if w.support != support || w.scope != scope {
        return Err("relation不適合の元支持・Scopeが違う".into());
    }
    if graph.get(w.left)?.ty == NodeType::Construction(T::Operation) {
        let a = crate::observed::public_compose::op(graph, w.left)?;
        let b = crate::observed::public_compose::op(graph, w.right)?;
        let (asource, atarget, _, _) = crate::observed::public_compose::components(graph, w.left)?;
        let (bsource, btarget, _, _) = crate::observed::public_compose::components(graph, w.right)?;
        let expected = if a.source() != b.source() {
            Some((asource, bsource))
        } else if a.target() != b.target() {
            Some((atarget, btarget))
        } else {
            None
        };
        if expected.is_none()
            || w.incompatible != expected
            || w.equal.is_some()
            || w.kind != "relation"
        {
            return Err("relationの元Operation端点が違う".into());
        }
        return Ok(());
    }
    let a = operand_path(graph, w.left)?;
    let b = operand_path(graph, w.right)?;
    let expected = if a.object() != b.object() {
        Some((a.object(), b.object()))
    } else if a.target() != b.target() {
        Some((a.target(), b.target()))
    } else {
        None
    };
    if let Some((left, right)) = expected {
        if graph.scalar(x)? != &left || graph.scalar(y)? != &right {
            return Err("relation不適合の実端点が違う".into());
        }
    } else if a.reading != b.reading {
        // Reading値は順に転記する。結論の条件辺では両方が既出である。
        for (reference, path, reading) in [(x, w.left, &a.reading), (y, w.right, &b.reading)] {
            if reference.0 < graph.nodes.len()
                && !matches!(part(graph,reference,w)?,Part::Reading{path:actual,value} if *actual==path && value==&Scalar::Text(reading.clone()))
            {
                return Err("relation不適合の実readingが違う".into());
            }
        }
    } else {
        return Err("適合するPathを不適合として返した".into());
    }
    Ok(())
}

fn proof_metadata(
    graph: &Graph,
    model: &Congruence,
    dependencies: &[NodeRef],
) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
    let mut support = model.support.clone();
    let mut scope = model.scope.clone();
    for reference in dependencies {
        let node = graph.get(*reference)?;
        support.extend(node.support.iter().cloned());
        scope.merge(&node.scope);
    }
    support.sort();
    support.dedup();
    Ok((support, scope))
}
