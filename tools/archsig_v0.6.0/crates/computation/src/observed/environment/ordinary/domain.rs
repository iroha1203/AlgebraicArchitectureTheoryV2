//! The original In collection is normalized once; members consume its checked
//! positions. Raw validation reconstructs this same local recipe from real refs.
use super::*;

pub(in crate::observed) struct InDomain {
    pub producer: NodeRef,
    pub domain: NodeRef,
    pub elements_len: usize,
}
struct Prepared {
    element: Type,
    value: Option<Scalar>,
    scope: Scope,
    domain_scope: Scope,
    support: Support,
}
fn prepare(
    env: &Environment<'_>,
    graph: &Graph,
    source: NodeRef,
    input: NodeRef,
    limit: usize,
) -> Result<Prepared, ValidationFailure> {
    let context = env.current_context(graph);
    if source.0 >= limit
        || input.0 >= limit
        || graph.context_at(source.0) != context
        || graph.context_at(input.0) != context
    {
        return Err(internal!("In域のSource/collection先行性・Contextが違う").into());
    }
    let span = env.expression_span(graph, source)?;
    let bindings = env.expression_bindings(graph, source)?;
    let law = env.indexes.inputs.law();
    let id = *law
        .program()
        .expressions
        .get(&span)
        .ok_or(internal!("In域の元量化ASTがない"))?;
    let (domain, element) = env
        .ordinary_collection_domain(id)?
        .ok_or(internal!("局所collection域の元型が未対応"))?;
    let comprehension = matches!(law.exprs()[id].kind, ExprKind::Comprehension { .. });
    let node = graph.get(input)?;
    let Some(Payload::Evaluation {
        expression,
        bindings: actual,
        value,
        environment,
        ..
    }) = &node.payload
    else {
        return Err(internal!("In collectionがEvaluationでない").into());
    };
    if expression.0 >= input.0
        || graph.context_at(expression.0) != context
        || env.expression_span(graph, *expression)? != law.exprs()[domain].span
        || env.expression_bindings(graph, *expression)? != bindings
        || actual != bindings
        || node.ty
            != NodeType::Evaluation(
                law.expr_type(domain)
                    .ok_or(internal!("In collection元型がない"))?
                    .clone(),
            )
        || *environment != env.state.architecture_ref()
    {
        return Err(internal!("In collectionの元AST/束縛/型/実環境が違う").into());
    }
    let failed = node
        .reasons
        .iter()
        .any(|reason| matches!(reason.kind, ReasonKind::ConditionFailed { .. }));
    let pending = env.evaluation_condition_pending(graph, input)?;
    #[cfg(test)]
    data::observe_actual(span, context, "in_domain_normalize", 0);
    let value = value
        .filter(|_| !failed && !pending)
        .map(|reference| {
            if reference.0 >= input.0 {
                return Err(internal!("In collection値が実Evalより先行しない").into());
            }
            let value = graph.scalar(reference)?;
            match value {
                Scalar::Set { element: ty, .. } if *ty == element => Ok(value.clone()),
                Scalar::List { element: ty, .. } if comprehension && *ty == element => {
                    Ok(value.clone())
                }
                Scalar::List { element: ty, items } if *ty == element => {
                    #[cfg(test)]
                    data::observe_actual(span, context, "in_set_normalization", 0);
                    data::set(element.clone(), items, &env.control)
                }
                _ => Err(internal!("In collectionが元要素型のList/Setでない").into()),
            }
        })
        .transpose()?;
    let mut domain_scope = node.scope.clone();
    if !comprehension {
        let spec = quantifier::spec(law, id, &env.control)?;
        domain_scope.add_quantifier(spec.descriptor(None, Some(context)));
        env.order_quantifier_scope(graph, source, &mut domain_scope)?;
    }
    Ok(Prepared {
        element,
        value,
        scope: node.scope.clone(),
        domain_scope,
        support: node.support.clone(),
    })
}
fn scalar(
    value: Scalar,
    rule: Rule,
    arguments: Vec<NodeRef>,
    scope: Scope,
    support: Support,
) -> Node {
    Node {
        ty: NodeType::Value(value.ty()),
        payload: Some(Payload::scalar(value)),
        rule,
        arguments,
        support,
        scope,
        evidence: vec![],
        judgment: None,
        reasons: vec![],
    }
}
fn domain(
    source: NodeRef,
    input: NodeRef,
    set: NodeRef,
    elements: Vec<NodeRef>,
    p: &Prepared,
) -> Node {
    Node {
        ty: NodeType::Domain,
        payload: Some(Payload::Domain {
            ty: p.element.clone(),
            elements: elements.clone(),
        }),
        rule: Rule::InDomain,
        arguments: [source, input, set].into_iter().chain(elements).collect(),
        scope: p.domain_scope.clone(),
        support: p.support.clone(),
        evidence: vec![],
        judgment: None,
        reasons: vec![],
    }
}
// This private commit accepts only nodes built above from a completed local
// recipe. Credit belongs to the exact immutable Graph snapshot; a later cold or
// changed-prefix consumer still takes independent validate_in_domain.
fn commit(
    env: &Environment<'_>,
    graph: &mut Graph,
    node: Node,
    committed: &mut impl FnMut(NodeRef, &Scope),
) -> Result<NodeRef, ValidationFailure> {
    let scope = node.scope.clone();
    let index = graph.nodes.len();
    let context = graph.active;
    let reference = graph.push_with_metadata(node, |reference| committed(reference, &scope))?;
    env.validation_graph_session(graph, || {
        env.results
            .cache
            .borrow_mut()
            .checked
            .insert((context, index));
        Ok(())
    })?;
    Ok(reference)
}
impl Environment<'_> {
    pub(in crate::observed) fn construct_in_domain(
        &self,
        graph: &mut Graph,
        source: NodeRef,
        input: NodeRef,
        mut committed: impl FnMut(NodeRef, &Scope),
    ) -> Result<Option<super::InDomain>, ValidationFailure> {
        if self.state.validation_depth.get() != 0 {
            return Err(internal!("raw検査中にIn域の通常構築を開始した").into());
        }
        self.validation_graph_session(graph, || {
            for reference in [source, input] {
                if reference.0 >= graph.nodes.len() {
                    return Err(internal!("In域の実入力が未出").into());
                }
                self.validate_at(graph, graph.get(reference)?, reference.0)?;
            }
            Ok(())
        })?;
        let mut p = prepare(self, graph, source, input, graph.nodes.len())?;
        let Some(value) = p.value.take() else {
            return Ok(None);
        };
        let (Scalar::List { items, .. } | Scalar::Set { items, .. }) = &value else {
            unreachable!()
        };
        let count = items.len();
        let set = commit(
            self,
            graph,
            scalar(
                value,
                Rule::InSet,
                vec![source, input],
                p.scope.clone(),
                p.support.clone(),
            ),
            &mut committed,
        )?;
        let mut members = Vec::with_capacity(count);
        for position in 0..count {
            self.tick()?;
            let (Scalar::List { items, .. } | Scalar::Set { items, .. }) = graph.scalar(set)?
            else {
                unreachable!()
            };
            let value = items[position].clone();
            members.push(commit(
                self,
                graph,
                scalar(
                    value,
                    Rule::InMember { position },
                    vec![set],
                    p.scope.clone(),
                    p.support.clone(),
                ),
                &mut committed,
            )?);
        }
        let reference = commit(
            self,
            graph,
            domain(source, input, set, members, &p),
            &mut committed,
        )?;
        Ok(Some(InDomain {
            producer: set,
            domain: reference,
            elements_len: count,
        }))
    }
    pub(in crate::observed) fn validate_in_domain(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if !matches!(
            node.rule,
            Rule::InSet | Rule::InMember { .. } | Rule::InDomain
        ) {
            return Ok(false);
        }
        for reference in &node.arguments {
            self.tick()?;
            if reference.0 >= limit || graph.context_at(reference.0) != self.current_context(graph)
            {
                return Err(internal!("In域recipeの実依存が先行する同Contextでない").into());
            }
            self.validate_at(graph, graph.get(*reference)?, reference.0)?;
        }
        if let Some(value) = node.scalar_payload() {
            data::check(value, self.indexes.inputs.law(), &self.control)?;
        }
        let expected = match node.rule {
            Rule::InSet => {
                let [source, input] = node.arguments.as_slice() else {
                    return Err(internal!("In Setの元入力辺が違う").into());
                };
                let mut p = prepare(self, graph, *source, *input, limit)?;
                let value = p
                    .value
                    .take()
                    .ok_or(internal!("未知In collectionから既知Setを作った"))?;
                let (
                    Scalar::List {
                        items: expected, ..
                    }
                    | Scalar::Set {
                        items: expected, ..
                    },
                    Some(Scalar::List { items: actual, .. } | Scalar::Set { items: actual, .. }),
                ) = (&value, node.scalar_payload())
                else {
                    return Err(internal!("In Set payloadの型が違う").into());
                };
                if expected.len() != actual.len() {
                    return Err(internal!("In Set全数が元collectionと違う").into());
                }
                let span = self.expression_span(graph, *source)?;
                let id = self.indexes.inputs.law().program().expressions[&span];
                let extensional = matches!(
                    self.indexes.inputs.law().exprs()[id].kind,
                    ExprKind::Comprehension { .. }
                ) && matches!(value, Scalar::Set { .. });
                if extensional {
                    if !data::equal(
                        node.scalar_payload().ok_or(internal!("collection値無し"))?,
                        &value,
                        &self.control,
                    )? {
                        return Err(internal!("内包Setの元collection外延が違う").into());
                    }
                } else {
                    for (actual, expected) in actual.iter().zip(expected) {
                        self.tick()?;
                        if !data::equal(actual, expected, &self.control)? {
                            return Err(internal!("In collectionの元順序が違う").into());
                        }
                    }
                }
                scalar(
                    value,
                    Rule::InSet,
                    vec![*source, *input],
                    p.scope,
                    p.support,
                )
            }
            Rule::InMember { position } => {
                let [set] = node.arguments.as_slice() else {
                    return Err(internal!("In memberのSet辺が違う").into());
                };
                let producer = graph.get(*set)?;
                let Some(Scalar::List { items, .. } | Scalar::Set { items, .. }) =
                    producer.scalar_payload()
                else {
                    return Err(internal!("In member producerがSetでない").into());
                };
                if producer.rule != Rule::InSet {
                    return Err(internal!("In member producer規則が違う").into());
                }
                let value = items
                    .get(position)
                    .ok_or(internal!("In member位置が域外"))
                    .cloned()?;
                scalar(
                    value,
                    Rule::InMember { position },
                    vec![*set],
                    producer.scope.clone(),
                    producer.support.clone(),
                )
            }
            Rule::InDomain => {
                let [source, input, set, rest @ ..] = node.arguments.as_slice() else {
                    return Err(internal!("In Domainの元辺がない").into());
                };
                let producer = graph.get(*set)?;
                let Some(Scalar::List { element, items } | Scalar::Set { element, items }) =
                    producer.scalar_payload()
                else {
                    return Err(internal!("In Domain Set producerがない").into());
                };
                if producer.rule != Rule::InSet || producer.arguments != [*source, *input] {
                    return Err(internal!("In Domainが別collection producerを指す").into());
                }
                let id = *self
                    .indexes
                    .inputs
                    .law()
                    .program()
                    .expressions
                    .get(&self.expression_span(graph, *source)?)
                    .ok_or(internal!("In Domain元ASTがない"))?;
                let (_, expected_element) = self
                    .ordinary_collection_domain(id)?
                    .ok_or(internal!("In Domain元collection型が未対応"))?;
                if *element != expected_element || rest.len() != items.len() {
                    return Err(internal!("In Domain型/完全coverage件数が違う").into());
                }
                let mut scope = producer.scope.clone();
                if matches!(
                    self.indexes.inputs.law().exprs()[id].kind,
                    ExprKind::Quant { .. }
                ) {
                    let spec = quantifier::spec(self.indexes.inputs.law(), id, &self.control)?;
                    scope.add_quantifier(spec.descriptor(None, Some(self.current_context(graph))));
                    scope.order_quantifiers_like(&graph.get(*source)?.scope);
                }
                for (position, member) in rest.iter().enumerate() {
                    let member = graph.get(*member)?;
                    if member.rule != (Rule::InMember { position }) || member.arguments != [*set] {
                        return Err(internal!("In Domain位置/実memberが違う").into());
                    }
                }
                let p = Prepared {
                    element: element.clone(),
                    value: None,
                    scope: producer.scope.clone(),
                    domain_scope: scope,
                    support: producer.support.clone(),
                };
                domain(*source, *input, *set, rest.to_vec(), &p)
            }
            _ => unreachable!(),
        };
        if !node.matches_with_support(&expected, &self.control)? {
            return Err(internal!("In域の値/順序/支持/Scope/完全recipeが違う").into());
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests;
