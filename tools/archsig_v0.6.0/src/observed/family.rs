//! 宣言parameter族の元署名・有限全域と、既出DAGからの実instance照合。
use super::*;
use crate::law::{
    ast::{QuantKind, Role},
    model::{Param, Signature},
};

pub(in crate::observed) struct Plan {
    pub dependent: bool,
    pub parameters: Vec<Param>,
    pub free: Vec<Param>,
    pub unbound: Vec<Param>,
    pub numeric: Vec<Param>,
    pub body: usize,
    pub guard: Option<usize>,
}
impl Environment<'_> {
    pub(in crate::observed) fn family_plan(
        &self,
        request: &Request,
    ) -> Result<Option<Plan>, ValidationFailure> {
        if request.kind != QuestionKind::Check {
            return Ok(None);
        }
        let d = self
            .inputs
            .law()
            .declarations
            .get(request.declaration().ok_or("元要求に宣言がない")?)
            .ok_or("族の元Lawがない")?;
        let Signature::Law {
            params,
            guard,
            body,
            ..
        } = &d.signature
        else {
            return Ok(None);
        };
        let free: Vec<_> = params
            .iter()
            .filter(|p| {
                !request
                    .arguments
                    .iter()
                    .any(|a| a.name == format!("bind.{}", p.name))
            })
            .cloned()
            .collect();
        let (mut numeric, mut unbound) = (Vec::new(), Vec::new());
        for p in &free {
            self.tick()?;
            if self.universal_symbolic_type(&p.ty.erase())? {
                numeric.push(p.clone());
            } else {
                unbound.push(p.clone());
            }
        }
        if unbound.is_empty() {
            return Ok(None);
        }
        let mut dependent = false;
        for p in params {
            self.tick()?;
            dependent |= p.ty != p.ty.erase();
            if p.ty != p.ty.erase()
                && !self.fixed_owned_binding(request, p)?
                && !self.deferred_owned_binding(request, p)?
                && request
                    .constraints
                    .iter()
                    .any(|c| c.parameter == p.name && c.dynamic)
                && request.arguments.iter().any(|argument| {
                    argument.name == format!("bind.{}", p.name)
                        && (matches!(argument.value, Selector::Answer { .. })
                            || matches!(&p.ty, Type::Owned(_, owner)
                                if request.arguments.iter().any(|owner_argument|
                                    owner_argument.name == format!("bind.{owner}")
                                    && matches!(owner_argument.value, Selector::Answer { .. }))))
                })
            {
                // 固定値の所属不適合を空の全称域に変えない。元入力再検査も同じ境界を使う。
                return Err(ValidationFailure::UnsupportedExpression {
                    location: Location::Law { span: p.span },
                    feature: "依存Law族の固定Owned束縛の動的所属制約".into(),
                });
            }
        }
        for p in params {
            self.tick()?;
            let finite_type = p.ty.erase();
            if unbound.iter().any(|u| u.name == p.name)
                && !super::super::finite::supported(&finite_type, self.inputs.law(), &self.control)?
            {
                return Err(ValidationFailure::UnsupportedExpression {
                    location: Location::Law { span: p.span },
                    feature: format!("未束縛Law parameter `{}` の未対応有限型・依存owner", p.name),
                });
            }
        }
        Ok(Some(Plan {
            dependent,
            parameters: params.clone(),
            free,
            unbound,
            numeric,
            body: *body,
            guard: *guard,
        }))
    }
    pub(in crate::observed) fn family_order_scope(
        &self,
        plan: &Plan,
        scope: &mut Scope,
    ) -> Result<(), ValidationFailure> {
        for _ in &scope.quantifiers {
            self.tick()?;
        }
        scope.quantifiers.sort_by_key(|q| {
            plan.parameters
                .iter()
                .position(|p| p.span == q.occurrence && p.name == q.name && p.ty.erase() == q.ty)
                .unwrap_or(plan.parameters.len())
        });
        Ok(())
    }
    pub(in crate::observed) fn family_merge_scope(
        &self,
        plan: &Plan,
        scope: &mut Scope,
        domains: &[NodeRef],
        context: super::super::call::Context,
    ) -> Result<(), ValidationFailure> {
        // 固定Answerの全域を残し、今回の自由parameterだけを実Domainへ更新する。
        scope.merge_quantifiers(&Scope {
            quantifiers: self.family_descriptors(plan, domains, context),
            ..Scope::default()
        });
        self.family_order_scope(plan, scope)
    }
    pub(in crate::observed) fn family_descriptors(
        &self,
        plan: &Plan,
        domains: &[NodeRef],
        context: super::super::call::Context,
    ) -> Vec<Quantifier> {
        plan.free
            .iter()
            .map(|p| Quantifier {
                kind: QuantKind::Forall,
                name: p.name.clone(),
                ty: p.ty.erase(),
                domain: plan
                    .unbound
                    .iter()
                    .position(|finite| finite.name == p.name)
                    .and_then(|i| domains.get(i))
                    .copied(),
                occurrence: p.span,
                context: (!matches!(p.ty, Type::Z | Type::Q)).then_some(context),
            })
            .collect()
    }
    fn family_source_ref(&self, graph: &Graph, r: NodeRef) -> Result<bool, ValidationFailure> {
        Ok(
            matches!(&graph.get(r)?.payload,Some(Payload::Expression {parameters,..}) if !parameters.is_empty()),
        )
    }
    /// 有限Law族の元whole Source。数値全域の各call出現とは区別する。
    pub(in crate::observed) fn family_source_root(
        &self,
        graph: &Graph,
        source: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        if !self.family_source_ref(graph, source)? {
            return Ok(false);
        }
        let context = graph.context_at(source.0);
        if context.frame.is_some() || context.iteration.is_some() || context.instance.is_some() {
            return Ok(false);
        }
        let request = graph
            .requests
            .get(context.request)
            .ok_or("族Sourceの元Requestがない")?;
        let Some(plan) = self.family_plan(request)? else {
            return Ok(false);
        };
        let Some(Payload::Expression {
            location: Location::Law { span },
            parameters,
            ..
        }) = &graph.get(source)?.payload
        else {
            return Ok(false);
        };
        Ok((*span == self.inputs.law().exprs[plan.body].span
            || Some(*span) == plan.guard.map(|g| self.inputs.law().exprs[g].span))
            && *parameters
                == plan
                    .free
                    .iter()
                    .map(|p| (p.name.clone(), p.ty.erase()))
                    .collect::<Vec<_>>())
    }

    pub(super) fn family_request<'g>(
        &self,
        graph: &'g Graph,
        source: NodeRef,
    ) -> Result<(&'g Request, Plan), ValidationFailure> {
        let context = graph.context_at(source.0);
        if context.frame.is_some() || context.iteration.is_some() || context.instance.is_some() {
            return Err("族Sourceがroot以外にある".into());
        }
        let request = graph
            .requests
            .get(context.request)
            .ok_or("族Sourceの元Requestがない")?;
        let plan = self
            .family_plan(request)?
            .ok_or("元Requestが未束縛Law族でない")?;
        self.source_matches(graph, source, plan.body)?;
        Ok((request, plan))
    }
    fn family_source(
        &self,
        graph: &Graph,
        node: &Node,
        context: super::super::call::Context,
    ) -> Result<Plan, ValidationFailure> {
        let request = graph
            .requests
            .get(context.request)
            .ok_or("族Sourceの元Requestがない")?;
        let plan = self
            .family_plan(request)?
            .ok_or("元Requestが未束縛Law族でない")?;
        let Some(Payload::Expression {
            location: Location::Law { span },
            parameters,
            bindings,
        }) = &node.payload
        else {
            return Err("族の元Sourceがない".into());
        };
        let d =
            &self.inputs.law().declarations[request.declaration().ok_or("元要求に宣言がない")?];
        if context.frame.is_some()
            || context.iteration.is_some()
            || context.instance.is_some()
            || (*span != self.inputs.law().exprs[plan.body].span
                && Some(*span) != plan.guard.map(|g| self.inputs.law().exprs[g].span))
            || parameters
                != &plan
                    .free
                    .iter()
                    .map(|p| (p.name.clone(), p.ty.erase()))
                    .collect::<Vec<_>>()
            || node.ty != NodeType::Expression(Type::Bool)
            || !matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span:actual}} if actual==span)
            || !node.support.is_empty()
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
            || node.judgment.is_some()
            || node.arguments != self.source_arguments(graph, *span, bindings)?
        {
            return Err("族Sourceの元parameter・出現・辺が違う".into());
        }
        let mut scope = Scope::default();
        scope.readings.insert(d.reading.clone());
        scope.merge(&self.architecture_scope());
        scope.assignments = !plan.numeric.is_empty();
        let fixed: Vec<_> = plan
            .parameters
            .iter()
            .filter(|p| !plan.free.iter().any(|u| u.name == p.name))
            .collect();
        if bindings.len() != fixed.len() {
            return Err("族Sourceの固定束縛数が違う".into());
        }
        for (p, b) in fixed.iter().zip(bindings) {
            self.tick()?;
            if let Some(check) = self.require_owned_binding(graph, request, p, b.value)? {
                scope.merge(&graph.get(check)?.scope);
            }
            if p.name != b.name || p.ty.erase() != b.ty {
                return Err("族Source固定署名が違う".into());
            }
            let selected = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
                .ok_or("固定selectorがない")?;
            match &selected.value {
                selector @ Selector::Answer { .. } => {
                    self.answer_binding_matches(graph, selector, b.value, p.span)?;
                }
                Selector::Subject { snapshot, subject } => {
                    let actual = self.subject(snapshot, subject)?;
                    if graph.scalar(b.value)?
                        != &(Scalar::Subject {
                            snapshot: snapshot.clone(),
                            subject: subject.clone(),
                            entity: actual.ty.clone(),
                        })
                    {
                        return Err("固定subject identityが違う".into());
                    }
                    if graph.context_at(b.value.0) != context {
                        return Err("固定bindingが別Request producer".into());
                    }
                }
                _ => return Err("固定束縛が元subject/Answer selectorでない".into()),
            }
            self.validate_at(graph, graph.get(b.value)?, b.value.0)?;
            scope.merge(&graph.get(b.value)?.scope);
        }
        scope.completions |= context.case.is_some();
        self.family_merge_scope(&plan, &mut scope, &[], context)?;
        if node.scope != scope {
            return Err("族SourceのScopeが元宣言と違う".into());
        }
        Ok(plan)
    }
    pub(in crate::observed) fn family_product(
        &self,
        types: &[Type],
        observer: &mut dyn FnMut(&'static str, usize),
    ) -> Result<super::super::finite::Enumeration, ValidationFailure> {
        if self.object_domain().is_none() {
            return self.finite_values(
                &if types.len() == 1 {
                    types[0].clone()
                } else {
                    Type::Tuple(types.to_vec())
                },
                observer,
            );
        }
        let mut result = super::super::finite::Enumeration::default();
        let mut rows: Vec<Vec<Scalar>> = vec![vec![]];
        for ty in types {
            let family = self.family_values(ty, observer)?;
            result.scope.merge(&family.scope);
            result.support.extend(family.support);
            let mut next = vec![];
            for row in rows {
                for value in &family.values {
                    self.tick()?;
                    observer("type_enum", next.len());
                    let mut row = row.clone();
                    row.push(value.clone());
                    next.push(row);
                }
            }
            rows = next;
        }
        result.values = rows
            .into_iter()
            .map(|mut row| {
                if types.len() == 1 {
                    row.remove(0)
                } else {
                    Scalar::Tuple(row)
                }
            })
            .collect();
        result.support.sort();
        result.support.dedup();
        Ok(result)
    }
    pub(in crate::observed) fn family_values(
        &self,
        ty: &Type,
        observer: &mut dyn FnMut(&'static str, usize),
    ) -> Result<super::super::finite::Enumeration, ValidationFailure> {
        let enumeration = self.finite_values(ty, observer)?;
        let mut domain = super::owned_type::TypeDomain {
            values: Some(enumeration.values),
            scope: enumeration.scope,
            support: enumeration.support,
            missing: vec![],
            owners: vec![],
            type_span: (0, 0),
        };
        self.restrict_object_domain(ty, &mut domain)?;
        Ok(super::super::finite::Enumeration {
            values: domain.values.ok_or("完成対象のparameter域が未確定")?,
            scope: domain.scope,
            support: domain.support,
        })
    }

    fn family_domains(
        &self,
        graph: &Graph,
        source: NodeRef,
        domains: &[NodeRef],
        plan: &Plan,
    ) -> Result<Scope, ValidationFailure> {
        if plan.dependent {
            return self.dependent_family_domains(graph, source, domains, plan);
        }
        if domains.len() != plan.unbound.len() {
            return Err("parameter域の個数が違う".into());
        }
        let mut scope = graph.get(source)?.scope.clone();
        for (p, &domain) in plan.unbound.iter().zip(domains) {
            self.tick()?;
            let node = graph.get(domain)?;
            if !matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span}} if *span==p.span)
                || node.arguments.first() != Some(&source)
            {
                return Err("parameter域が元署名の出現と違う".into());
            }
            self.validate_at(graph, node, domain.0)?;
            scope.merge(&node.scope);
        }
        self.family_merge_scope(plan, &mut scope, domains, graph.context_at(source.0))?;
        Ok(scope)
    }
    fn family_domain_parts(
        &self,
        graph: &Graph,
        domain: NodeRef,
    ) -> Result<(NodeRef, Vec<NodeRef>, Plan), ValidationFailure> {
        let node = graph.get(domain)?;
        let source = *node.arguments.first().ok_or("直積の元Sourceがない")?;
        let (_, plan) = self.family_request(graph, source)?;
        if plan.dependent {
            return self.dependent_family_domain_parts(graph, domain, source, plan);
        }
        let count = plan.unbound.len();
        let domains = if count == 1 {
            vec![domain]
        } else {
            node.arguments
                .get(1..1 + count)
                .ok_or("直積のparameter域がない")?
                .to_vec()
        };
        self.validate_at(graph, node, domain.0)?;
        Ok((source, domains, plan))
    }
    pub(super) fn family_instance_inputs(
        &self,
        graph: &Graph,
        index: usize,
    ) -> Result<FrameInputs, ValidationFailure> {
        let record = graph.instances.get(index).ok_or("実instanceがない")?;
        if record.caller.instance.is_some()
            || record.caller.frame.is_some()
            || record.caller.iteration.is_some()
            || graph.context_at(record.source.0) != record.caller
            || graph.context_at(record.domain.0) != record.caller
        {
            return Err("instanceの元Contextが違う".into());
        }
        let (source, domains, plan) = self.family_domain_parts(graph, record.domain)?;
        if source != record.source {
            return Err("instanceの元族Sourceが違う".into());
        }
        let Some(Payload::Domain { elements, .. }) = &graph.get(record.domain)?.payload else {
            return Err("instanceの実直積がない".into());
        };
        if !elements.contains(&record.member) {
            return Err("instance memberが元直積の元でない".into());
        }
        let items = family_items(graph.scalar(record.member)?, plan.unbound.len())?;
        let fixed = self.expression_bindings(graph, source)?;
        let base = self.family_domains(graph, source, &domains, &plan)?;
        let mut bindings = Vec::new();
        let mut variables = BTreeMap::new();
        for p in &plan.parameters {
            self.tick()?;
            if plan
                .numeric
                .iter()
                .any(|parameter| parameter.name == p.name)
            {
                if self.universal_context.borrow().is_some() {
                    variables.insert(
                        p.name.clone(),
                        self.universal_parameter_value(p.span, &p.name, &p.ty, &base)?,
                    );
                }
                continue;
            }
            let value = if let Some(i) = plan.unbound.iter().position(|u| u.name == p.name) {
                let expected = items.get(i).ok_or("instance tuple位置がない")?;
                let mut found = None;
                for (id, node) in graph
                    .nodes
                    .iter()
                    .enumerate()
                    .take(self.cutoff.get().min(graph.nodes.len()))
                {
                    self.tick()?;
                    let c = graph.context_at(id);
                    if c.instance == Some(index)
                        && c.frame.is_none()
                        && c.iteration.is_none()
                        && node.arguments == [source, record.domain, record.member]
                        && matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span}} if *span==p.span)
                        && matches!(&node.payload,Some(Payload::Scalar(s)) if s==expected)
                    {
                        if found.is_some() {
                            return Err("同じinstanceの元parameter値が重複".into());
                        }
                        found = Some(NodeRef(id));
                    }
                }
                found.ok_or("実instance parameter producerがない")?
            } else {
                fixed
                    .iter()
                    .find(|b| b.name == p.name)
                    .ok_or("固定bindingがない")?
                    .value
            };
            let scalar = graph.scalar(value)?.clone();
            if plan.dependent {
                self.validate_at(graph, graph.get(value)?, value.0)?;
            }
            if scalar.ty() != p.ty.erase() {
                return Err("実instance parameter型が違う".into());
            }
            let b = Binding {
                name: p.name.clone(),
                ty: p.ty.erase(),
                value,
            };
            variables.insert(
                p.name.clone(),
                SourceValue {
                    condition_failed: false,
                    condition_pending: false,
                    symbolic: None,
                    comparison: None,
                    affine: super::super::affine::constant(&scalar, &self.control)?.map(Box::new),
                    scope: base.clone(),
                    known_value: Some(scalar),
                    support: graph.get(value)?.support.clone(),
                    scalar_scope: Some(graph.get(value)?.scope.clone()),
                },
            );
            bindings.push(b);
        }
        Ok((bindings, variables, base))
    }
    /// 特別扱いするのは実族の既出辺を持つnodeだけ。通常式は既存の厳密照合へ進む。
    pub(super) fn validate_family_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let context = self.current_context(graph);
        if matches!(&node.payload,Some(Payload::Expression {parameters,..}) if !parameters.is_empty())
        {
            self.family_source(graph, node, context)?;
            return Ok(true);
        }
        if self.validate_dependent_family_node(graph, node, limit)? {
            return Ok(true);
        }
        if let Some(&source) = node.arguments.first()
            && self.family_source_ref(graph, source)?
        {
            let (_, plan) = self.family_request(graph, source)?;
            self.validate_at(graph, graph.get(source)?, source.0)?;
            let d = &self.inputs.law().declarations[graph.requests
                [graph.context_at(source.0).request]
                .declaration()
                .ok_or("元要求に宣言がない")?];
            let origin = match &node.rule {
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                } => Some(*span),
                _ => None,
            };
            if (node.arguments.len() == 1
                || matches!(node.payload, Some(Payload::Domain { .. }))
                || origin == Some(d.span))
                && context != graph.context_at(source.0)
            {
                return Err("族Domain/memberが別Request・instanceに属す".into());
            }
            if let Some(Payload::Scalar(value)) = &node.payload {
                let p = plan.unbound.iter().position(|p| Some(p.span) == origin);
                let (expected_values, scope, support) = if let Some(p) = p {
                    let enumeration = self.family_values(&plan.unbound[p].ty, &mut |_, _| {})?;
                    let mut scope = graph.get(source)?.scope.clone();
                    scope.merge(&enumeration.scope);
                    if node.arguments.len() == 1 {
                        (enumeration.values, scope, enumeration.support)
                    } else {
                        let index = context.instance.ok_or("row値にinstance Contextがない")?;
                        let record = graph.instances.get(index).ok_or("row値のinstanceがない")?;
                        if context.request != record.caller.request
                            || context.frame.is_some()
                            || context.iteration.is_some()
                            || node.arguments != [record.source, record.domain, record.member]
                            || source != record.source
                        {
                            return Err("row値の元直積辺が違う".into());
                        }
                        let (_, domains, _) = self.family_domain_parts(graph, record.domain)?;
                        let Some(Payload::Domain { elements, .. }) =
                            &graph.get(record.domain)?.payload
                        else {
                            return Err("row域がない".into());
                        };
                        if !elements.contains(&record.member) {
                            return Err("rowが元直積にない".into());
                        }
                        let items = family_items(graph.scalar(record.member)?, plan.unbound.len())?;
                        (
                            vec![items[p].clone()],
                            self.family_domains(graph, source, &domains, &plan)?,
                            graph.get(record.domain)?.support.clone(),
                        )
                    }
                } else if origin == Some(d.span) {
                    let domains = node.arguments.get(1..).ok_or("直積member域辺がない")?;
                    let scope = self.family_domains(graph, source, domains, &plan)?;
                    let enumeration = self.family_product(
                        &plan
                            .unbound
                            .iter()
                            .map(|p| p.ty.clone())
                            .collect::<Vec<_>>(),
                        &mut |_, _| {},
                    )?;
                    (enumeration.values, scope, enumeration.support)
                } else {
                    return Err("族値の元parameter出現が違う".into());
                };
                data::check(value, self.inputs.law(), &self.control)?;
                if node.ty != NodeType::Value(value.ty())
                    || !data::contains(&expected_values, value, &self.control)?
                    || node.scope != scope
                    || node.support != support
                    || !node.evidence.is_empty()
                    || !node.reasons.is_empty()
                    || node.judgment.is_some()
                {
                    return Err("族memberの元型/値/Scope/支持が違う".into());
                }
                return Ok(true);
            }
            if let Some(Payload::Domain { ty, elements }) = &node.payload {
                let (enumeration, scope, offset) =
                    if let Some(p) = plan.unbound.iter().find(|p| Some(p.span) == origin) {
                        if ty != &p.ty {
                            return Err("parameter Domain型が違う".into());
                        }
                        let e = self.family_values(&p.ty, &mut |_, _| {})?;
                        let mut scope = graph.get(source)?.scope.clone();
                        scope.merge(&e.scope);
                        (e, scope, 1)
                    } else if origin == Some(d.span) {
                        let types: Vec<_> = plan.unbound.iter().map(|p| p.ty.clone()).collect();
                        if ty != &family_type(&types) {
                            return Err("直積Domain型が違う".into());
                        }
                        let count = plan.unbound.len();
                        let scope = self.family_domains(
                            graph,
                            source,
                            node.arguments.get(1..1 + count).ok_or("直積元域がない")?,
                            &plan,
                        )?;
                        (
                            self.family_product(&types, &mut |_, _| {})?,
                            scope,
                            1 + count,
                        )
                    } else {
                        return Err("族Domainの元parameter出現が違う".into());
                    };
                if node.ty != NodeType::Domain
                    || node.arguments.get(offset..) != Some(elements.as_slice())
                    || node.scope != scope
                    || node.support != enumeration.support
                    || !node.evidence.is_empty()
                    || !node.reasons.is_empty()
                    || node.judgment.is_some()
                    || elements.len() != enumeration.values.len()
                {
                    return Err("族Domainの全域/辺/Scope/支持が違う".into());
                }
                let mut seen = Vec::new();
                for &r in elements {
                    self.tick()?;
                    if r.0 >= limit {
                        return Err("族Domain元が未出".into());
                    }
                    let member = graph.get(r)?;
                    if member.arguments != node.arguments[..offset]
                        || !matches!((&member.rule,&node.rule),(Rule::Input {kind:"law",location:Location::Law {span:a}},Rule::Input {kind:"law",location:Location::Law {span:b}}) if a==b)
                    {
                        return Err("族Domainの元memberが別Source/parameter出現に属す".into());
                    }
                    self.validate_at(graph, member, r.0)?;
                    let v = graph.scalar(r)?;
                    if v.ty() != *ty
                        || !data::contains(&enumeration.values, v, &self.control)?
                        || data::contains(&seen, v, &self.control)?
                    {
                        return Err("族Domainに異型/欠落/重複がある".into());
                    }
                    seen.push(v.clone());
                }
                return Ok(true);
            }
        }
        if context.instance.is_some()
            && node.arguments.len() == 2
            && matches!(
                node.payload,
                Some(
                    Payload::Counterexample { .. }
                        | Payload::EvaluationEvidence { .. }
                        | Payload::Proposition { .. }
                )
            )
            && !self.family_template(graph, node.arguments[0])?
            && (graph.context_at(node.arguments[0].0) != context
                || graph.context_at(node.arguments[1].0) != context)
        {
            return Err("実rowの結論が別instance producerを消費している".into());
        }
        self.validate_family_application(graph, node, limit)
    }
}

pub(in crate::observed) fn family_type(types: &[Type]) -> Type {
    if types.len() == 1 {
        types[0].clone()
    } else {
        Type::Tuple(types.to_vec())
    }
}
pub(in crate::observed) fn family_items(
    value: &Scalar,
    count: usize,
) -> Result<Vec<Scalar>, ValidationFailure> {
    if count == 1 {
        Ok(vec![value.clone()])
    } else if let Scalar::Tuple(items) = value {
        if items.len() != count {
            return Err("実直積の成分数が違う".into());
        }
        Ok(items.clone())
    } else {
        Err("実直積memberがTupleでない".into())
    }
}

struct Aggregate {
    rows: Vec<NodeRef>,
    domain: NodeRef,
    scope: Scope,
    support: Vec<Fact>,
    reasons: Vec<Reason>,
    value: Option<bool>,
}
impl Environment<'_> {
    pub(super) fn family_template(
        &self,
        graph: &Graph,
        r: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        Ok(match &graph.get(r)?.payload {
            Some(Payload::LawInstance { body, .. }) => self.family_source_ref(graph, *body)?,
            _ => false,
        })
    }
    fn family_aggregate(
        &self,
        graph: &Graph,
        template: &Node,
    ) -> Result<Aggregate, ValidationFailure> {
        let Some(Payload::LawInstance {
            name,
            role,
            bindings,
            guard,
            body,
            occurrence,
        }) = &template.payload
        else {
            return Err("族LawInstanceがない".into());
        };
        let (request, plan) = self.family_request(graph, *body)?;
        let d =
            &self.inputs.law().declarations[request.declaration().ok_or("元要求に宣言がない")?];
        let Signature::Law {
            role: expected_role,
            ..
        } = &d.signature
        else {
            unreachable!()
        };
        if name != &d.name
            || occurrence != &(Location::Law { span: d.span })
            || *role
                != match expected_role {
                    Role::Required => "required",
                    Role::Optional => "optional",
                }
            || bindings != self.expression_bindings(graph, *body)?
            || template.arguments.first() != Some(body)
        {
            return Err("whole LawInstanceの元宣言/固定bindingが違う".into());
        }
        self.validate_at(graph, graph.get(*body)?, body.0)?;
        let offset = 1 + usize::from(guard.is_some());
        match (guard, plan.guard) {
            (Some(g), Some(id)) => {
                self.source_matches(graph, *g, id)?;
                self.validate_at(graph, graph.get(*g)?, g.0)?;
                if template.arguments.get(1) != Some(g)
                    || self.expression_bindings(graph, *g)? != bindings
                {
                    return Err("whole guardの元自由parameterが違う".into());
                }
            }
            (None, None) => {}
            _ => return Err("whole guardが元Lawと違う".into()),
        }
        let domain = *template
            .arguments
            .get(offset)
            .ok_or("wholeに実直積域がない")?;
        let (source, domains, actual_plan) = self.family_domain_parts(graph, domain)?;
        if source != *body || actual_plan.unbound != plan.unbound {
            return Err("whole直積が別の族Source".into());
        }
        let Some(Payload::Domain { elements, .. }) = &graph.get(domain)?.payload else {
            return Err("wholeの有限直積がない".into());
        };
        let count = elements.len();
        let concrete = template
            .arguments
            .get(offset + 1..offset + 1 + count)
            .ok_or("wholeに実row LawInstanceがない")?;
        let rows = template.arguments[offset + 1 + count..].to_vec();
        if rows.len() != count
            || concrete
                .iter()
                .enumerate()
                .any(|(i, r)| concrete[..i].contains(r))
        {
            return Err("wholeの実直積coverage件数が違う".into());
        }
        let mut scope = self.family_domains(graph, *body, &domains, &plan)?;
        let mut support = graph.get(domain)?.support.clone();
        let mut reasons = Vec::new();
        let mut seen = Vec::new();
        let mut value = Some(true);
        for (row_index, &row) in rows.iter().enumerate() {
            self.tick()?;
            let context = graph.context_at(row.0);
            let index = context.instance.ok_or("whole rowにinstanceがない")?;
            let record = graph
                .instances
                .get(index)
                .ok_or("whole rowの実instanceがない")?;
            if context.frame.is_some()
                || context.iteration.is_some()
                || context.request != graph.context_at(body.0).request
                || record.source != *body
                || record.domain != domain
                || !elements.contains(&record.member)
                || seen.contains(&record.member)
                || (plan.dependent && elements.get(row_index) != Some(&record.member))
            {
                return Err("wholeに別instance/欠落/重複rowがある".into());
            }
            seen.push(record.member);
            #[cfg(test)]
            data::observe_actual(
                d.span,
                self.current_context(graph),
                "family_recheck",
                seen.len() - 1,
            );
            self.tick()?;
            self.recheck_evaluation(graph, row)?;
            let (_, bs, v) = self.evaluation(graph, row)?;
            let candidates: Vec<_> = concrete
                .iter()
                .copied()
                .filter(|r| graph.context_at(r.0) == context)
                .collect();
            if candidates.len() != 1 {
                return Err("whole実rowとLawInstanceが一対一でない".into());
            }
            let concrete_instance = candidates[0];
            if plan.dependent && concrete.get(row_index) != Some(&concrete_instance) {
                return Err("依存wholeの実row LawInstance順が元域と違う".into());
            }
            self.validate_at(graph, graph.get(concrete_instance)?, concrete_instance.0)?;
            let Some(Payload::LawInstance {
                bindings: actual, ..
            }) = &graph.get(concrete_instance)?.payload
            else {
                return Err("whole実rowがLawInstanceでない".into());
            };
            if actual != bs {
                return Err("whole実rowとLawInstanceのbindingsが違う".into());
            }
            let previous = self.context.replace(Some(context));
            let connection = (|| -> Result<(), ValidationFailure> {
                if !plan.numeric.is_empty() {
                    // 数値rowのLawInstanceは、専用wholeを先行辺として検査済み。
                    // 通常のbody Evaluation/guard wrapperへ読み替えない。
                    if graph.get(concrete_instance)?.arguments.first() != Some(&row)
                        || !self.universal_owned_evaluation(graph, row)?
                    {
                        return Err("有限族の数値rowが当該全域wholeに接続しない".into());
                    }
                } else if self
                    .family_skipped(graph, graph.get(concrete_instance)?)?
                    .is_some()
                {
                    if graph.get(row)?.arguments.first() != Some(&concrete_instance) {
                        return Err("非適用rowが別LawInstanceに属す".into());
                    }
                } else {
                    self.instance_evaluation(graph, concrete_instance, row)?;
                }
                Ok(())
            })();
            self.context.set(previous);
            connection?;
            let previous = self.context.replace(Some(context));
            let inputs = self.family_instance_inputs(graph, index);
            self.context.set(previous);
            if inputs?.0 != *bs {
                return Err("whole row bindingsが元実直積と違う".into());
            }
            let b = graph.boolean(v)?;
            if b == Some(false) {
                value = Some(false);
            } else if b.is_none() && value != Some(false) {
                value = None;
            }
            scope.merge(&graph.get(row)?.scope);
            support.extend(graph.get(row)?.support.iter().cloned());
            reasons.extend(graph.get(row)?.reasons.iter().cloned());
        }
        support.sort();
        support.dedup();
        sort_reasons(&mut reasons);
        self.family_order_scope(&plan, &mut scope)?;
        Ok(Aggregate {
            rows,
            domain,
            scope,
            support,
            reasons,
            value,
        })
    }
    /// 元直積・LawInstanceとの接続を検査済みの数値rowに、実反例を結び付ける。
    fn family_numeric_counterexample(
        &self,
        graph: &Graph,
        evidence: NodeRef,
        row: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        self.validation_session(|| {
            self.tick()?;
            let previous = self.context.replace(Some(graph.context_at(row.0)));
            let previous_cutoff = self.cutoff.replace(row.0);
            let previous_universal = self.universal_context.replace(None);
            let previous_completion = self.completion_values.replace(Vec::new());
            let result = self.family_numeric_counterexample_in_context(graph, evidence, row);
            self.completion_values.replace(previous_completion);
            self.universal_context.replace(previous_universal);
            self.cutoff.set(previous_cutoff);
            self.context.set(previous);
            result
        })
    }
    fn family_numeric_counterexample_in_context(
        &self,
        graph: &Graph,
        evidence: NodeRef,
        row: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let proof = graph.get(evidence)?;
        if !matches!(proof.payload, Some(Payload::Counterexample { .. })) {
            return Ok(false);
        }
        let normalization = match proof.arguments.as_slice() {
            [_, _, normalization] | [_, normalization, _, _, _]
                if matches!(
                    graph.get(*normalization)?.payload,
                    Some(Payload::Normalization { .. })
                ) =>
            {
                *normalization
            }
            _ => return Ok(false),
        };
        self.recheck_evaluation(graph, row)?;
        if !self.universal_owned_evaluation(graph, row)? {
            return Ok(false);
        }
        self.validate_at(graph, proof, evidence.0)?;
        self.validate_at(graph, graph.get(normalization)?, normalization.0)?;
        let whole = graph.get(row)?;
        let (expression, _, value) = self.evaluation(graph, row)?;
        if graph.boolean(value)? != Some(false)
            || graph.context_at(evidence.0) != graph.context_at(row.0)
            || proof.scope != whole.scope
            || proof.support != whole.support
            || whole.evidence != [normalization]
        {
            return Ok(false);
        }
        Ok(match proof.arguments.as_slice() {
            [source, actual_whole, actual_normalization] => {
                *source == expression
                    && *actual_whole == row
                    && *actual_normalization == normalization
            }
            [source, actual_normalization, _, _, _] => {
                *source == expression && *actual_normalization == normalization
            }
            _ => false,
        })
    }
    fn family_skipped(
        &self,
        graph: &Graph,
        instance: &Node,
    ) -> Result<Option<(NodeRef, NodeRef)>, ValidationFailure> {
        let Some(Payload::LawInstance {
            body,
            guard: Some(guard),
            bindings,
            ..
        }) = &instance.payload
        else {
            return Ok(None);
        };
        if instance.arguments.first() != Some(body)
            || !matches!(graph.get(*body)?.ty, NodeType::Expression(_))
        {
            return Ok(None);
        }
        let context = self.current_context(graph);
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("非適用rowのRequestがない")?;
        let (expected_bindings, body_id, id) = if let Some(index) = context.instance {
            let expected = self.family_instance_inputs(graph, index)?;
            let plan = self.family_plan(request)?.ok_or("非適用rowの族がない")?;
            (
                expected.0,
                plan.body,
                plan.guard.ok_or("非適用rowに元guardがない")?,
            )
        } else if context.case.is_some() && context.frame.is_none() && context.iteration.is_none() {
            let declaration = &self.inputs.law().declarations
                [request.declaration().ok_or("元要求に宣言がない")?];
            let Signature::Law {
                params,
                body,
                guard: Some(id),
                ..
            } = &declaration.signature
            else {
                return Err("補完非適用の元Law/guardがない".into());
            };
            if params.len() != bindings.len()
                || request
                    .arguments
                    .iter()
                    .filter(|a| a.name.starts_with("bind."))
                    .count()
                    != params.len()
            {
                return Err("補完非適用の明示束縛数が違う".into());
            }
            for (parameter, binding) in params.iter().zip(bindings) {
                self.tick()?;
                let selector = request
                    .arguments
                    .iter()
                    .find(|argument| argument.name == format!("bind.{}", parameter.name))
                    .ok_or("補完非適用の元selectorがない")?;
                let Selector::Subject { snapshot, subject } = &selector.value else {
                    return Err("補完非適用に未対応selectorがある".into());
                };
                let producer = graph.get(binding.value)?;
                if parameter.name != binding.name
                    || parameter.ty.erase() != binding.ty
                    || graph.context_at(binding.value.0) != context
                    || !producer.arguments.is_empty()
                    || !matches!(
                        &producer.rule,
                        Rule::Input {
                            kind: "subject",
                            ..
                        }
                    )
                    || !matches!(graph.scalar(binding.value)?,Scalar::Subject {snapshot:actual_snapshot,subject:actual_subject,entity} if actual_snapshot==snapshot && actual_subject==subject && Type::Ref(entity.clone())==binding.ty)
                {
                    return Err("補完非適用の固定束縛producerが違う".into());
                }
                self.validate_at(graph, producer, binding.value.0)?;
            }
            (bindings.clone(), *body, *id)
        } else {
            return Err("非適用rowにinstance/caseがない".into());
        };
        self.source_matches(graph, *body, body_id)?;
        self.source_matches(graph, *guard, id)?;
        let g = *instance
            .arguments
            .get(1)
            .ok_or("非適用rowのguard実評価がない")?;
        self.recheck_evaluation(graph, g)?;
        let (expression, bs, value) = self.evaluation(graph, g)?;
        if graph.context_at(body.0) != self.current_context(graph)
            || graph.context_at(g.0) != self.current_context(graph)
            || self.expression_bindings(graph, *body)? != bindings
            || !family_clean(instance, "law_instance", &[])
        {
            return Err("非適用LawInstanceの元producer・規則が違う".into());
        }
        if *guard != expression
            || bs != bindings
            || bindings != &expected_bindings
            || graph.boolean(value)? != Some(false)
            || instance.arguments[2..] != bindings.iter().map(|b| b.value).collect::<Vec<_>>()
            || instance.scope != graph.get(g)?.scope
            || instance.support != graph.get(g)?.support
        {
            return Err("非適用rowが元guardfalse/実bindingsと違う".into());
        }
        let d =
            &self.inputs.law().declarations[request.declaration().ok_or("元要求に宣言がない")?];
        let Some(Payload::LawInstance {
            name,
            role,
            occurrence,
            ..
        }) = &instance.payload
        else {
            unreachable!()
        };
        let Signature::Law { role: r, .. } = &d.signature else {
            unreachable!()
        };
        if name != &d.name
            || occurrence != &(Location::Law { span: d.span })
            || *role
                != match r {
                    Role::Required => "required",
                    Role::Optional => "optional",
                }
        {
            return Err("非適用rowが元Lawと違う".into());
        }
        self.validate_at(graph, graph.get(*body)?, body.0)?;
        Ok(Some((*body, g)))
    }
    fn validate_family_application(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if let Some(Payload::LawInstance { body, .. }) = &node.payload {
            if self.family_source_ref(graph, *body)? {
                let a = self.family_aggregate(graph, node)?;
                if graph.context_at(body.0) != self.current_context(graph)
                    || node.scope != a.scope
                    || node.support != a.support
                    || !node.evidence.is_empty()
                    || !node.reasons.is_empty()
                    || !family_clean(node, "law_instance", &[])
                {
                    return Err("whole LawInstanceのScope/支持が違う".into());
                }
                return Ok(true);
            }
            if (self.current_context(graph).instance.is_some()
                || self.current_context(graph).case.is_some())
                && self.family_skipped(graph, node)?.is_some()
            {
                return Ok(true);
            }
        }
        let Some(&instance) = node.arguments.first() else {
            return Ok(false);
        };
        if self.family_template(graph, instance)? {
            self.validate_at(graph, graph.get(instance)?, instance.0)?;
            let a = self.family_aggregate(graph, graph.get(instance)?)?;
            let Some(Payload::LawInstance { body, bindings, .. }) = &graph.get(instance)?.payload
            else {
                unreachable!()
            };
            if node.scope != a.scope
                || node.support != a.support
                || self.current_context(graph) != graph.context_at(instance.0)
            {
                return Err("whole構成のScope/支持が違う".into());
            }
            match &node.payload {
                Some(Payload::Scalar(Scalar::Bool(v))) => {
                    if node.ty != NodeType::Value(Type::Bool)
                        || !family_clean(node, "evaluation", &[])
                        || Some(*v) != a.value
                        || (node.arguments.first() != Some(&instance)
                            || !family_refs(&node.arguments[1..], &a.rows))
                        || !node.evidence.is_empty()
                        || !node.reasons.is_empty()
                    {
                        return Err("whole値が元row集約と違う".into());
                    }
                }
                Some(Payload::Evaluation {
                    expression,
                    bindings: bs,
                    parts,
                    value,
                    applicability,
                    ..
                }) => {
                    let expected_args = std::iter::once(instance)
                        .chain(std::iter::once(a.domain))
                        .chain(a.rows.iter().copied())
                        .collect::<Vec<_>>();
                    if !family_clean(node, "evaluation", &a.reasons)
                        || node.ty != NodeType::Evaluation(Type::Bool)
                        || expression != body
                        || bs != bindings
                        || *applicability != "applicable"
                        || parts.len() != 1
                        || parts[0].location
                            != (Location::Law {
                                span: self.expression_span(graph, *body)?,
                            })
                        || !family_refs(&parts[0].children, &a.rows)
                        || parts[0].value != *value
                        || parts[0].residual.is_some()
                        || node.arguments.get(..2) != expected_args.get(..2)
                        || !family_refs(
                            node.arguments.get(2..).ok_or("whole row辺がない")?,
                            &a.rows,
                        )
                        || graph.boolean(*value)? != a.value
                    {
                        return Err("whole評価が元族/row/判断と違う".into());
                    }
                    if let Some(v) = value {
                        self.validate_at(graph, graph.get(*v)?, v.0)?;
                        if graph.get(*v)?.arguments.first() != Some(&instance) {
                            return Err("whole値が別producer".into());
                        }
                    }
                    if !reasons_equal(&node.reasons, &a.reasons) {
                        return Err("wholeが既読missingを落とした".into());
                    }
                }
                Some(Payload::FiniteExhaustion {
                    domain,
                    checked,
                    instances,
                }) => {
                    let evaluation = *node.arguments.get(1).ok_or("whole全検査に評価がない")?;
                    self.recheck_evaluation(graph, evaluation)?;
                    if !family_clean(node, "evidence", &[])
                        || node.ty != NodeType::Evidence
                        || node.arguments != [instance, evaluation]
                        || *domain != a.domain
                        || *checked != a.rows.len()
                        || instances.len() != a.rows.len()
                        || instances.iter().any(|r| !a.rows.contains(r))
                        || instances
                            .iter()
                            .enumerate()
                            .any(|(i, r)| instances[..i].contains(r))
                        || a.value != Some(true)
                        || !node.evidence.is_empty()
                        || !node.reasons.is_empty()
                    {
                        return Err("whole全検査coverageが元直積と違う".into());
                    }
                }
                Some(Payload::Proposition { instance: actual }) => {
                    let evaluation = *node.arguments.get(1).ok_or("whole命題に評価がない")?;
                    self.recheck_evaluation(graph, evaluation)?;
                    if node.ty != NodeType::Proposition
                        || !family_refs(&node.evidence, &node.evidence)
                        || !matches!(node.rule, Rule::Construction("proposition"))
                        || !reasons_equal(&node.reasons, &a.reasons)
                        || !node
                            .judgment
                            .as_ref()
                            .is_some_and(|j| reasons_equal(&j.reasons, &a.reasons))
                        || actual != &instance
                        || node.arguments != [instance, evaluation]
                        || node.judgment.as_ref().map(|j| j.status)
                            != Some(family_decision(a.value))
                    {
                        return Err("whole命題の元族/判断が違う".into());
                    }
                    graph.validate_proposition_evidence(node)?;
                    for &e in &node.evidence {
                        self.validate_at(graph, graph.get(e)?, e.0)?;
                    }
                    let full = node
                        .evidence
                        .iter()
                        .filter(|r| {
                            matches!(
                                graph.get(**r).map(|n| &n.payload),
                                Ok(Some(Payload::FiniteExhaustion { .. }))
                            )
                        })
                        .count();
                    if full != usize::from(a.value == Some(true)) {
                        return Err("whole全称判断の全検査証拠が違う".into());
                    }
                    for &row in &a.rows {
                        self.tick()?;
                        if graph.boolean(self.evaluation(graph, row)?.2)? == Some(false) {
                            let mut found = false;
                            for &e in &node.evidence {
                                self.tick()?;
                                if matches!(
                                    graph.get(e)?.payload,
                                    Some(Payload::Counterexample { .. })
                                ) && (self.family_numeric_counterexample(graph, e, row)?
                                    || graph.get(e)?.arguments.get(1) == Some(&row)
                                    || graph.evaluation_evidence_contains(row, e)?)
                                {
                                    found = true;
                                }
                            }
                            if !found {
                                return Err("wholeが実反例を落とした".into());
                            }
                        }
                    }
                }
                _ => return Err("wholeに未定のpayload".into()),
            }
            return Ok(true);
        }
        if (self.current_context(graph).instance.is_some()
            || self.current_context(graph).case.is_some())
            && let Some((body, guard)) = self.family_skipped(graph, graph.get(instance)?)?
        {
            match &node.payload {
                Some(Payload::Scalar(Scalar::Bool(true))) => {
                    if !family_clean(node, "evaluation", &[])
                        || node.ty != NodeType::Value(Type::Bool)
                        || graph.context_at(instance.0) != self.current_context(graph)
                        || node.arguments != [instance, guard]
                        || node.scope != graph.get(guard)?.scope
                        || node.support != graph.get(guard)?.support
                    {
                        return Err("非適用値が実guard由来でない".into());
                    }
                }
                Some(Payload::Evaluation {
                    expression,
                    bindings,
                    parts,
                    value,
                    applicability,
                    ..
                }) => {
                    let (_, bs, _) = self.evaluation(graph, guard)?;
                    let guard_node = graph.get(guard)?;
                    let Some(Payload::Evaluation {
                        expression: guard_source,
                        parts: guard_parts,
                        ..
                    }) = &guard_node.payload
                    else {
                        return Err("guard Evaluationがない".into());
                    };

                    if !family_clean(node, "evaluation", &guard_node.reasons)
                        || node.ty != NodeType::Evaluation(Type::Bool)
                        || graph.context_at(instance.0) != self.current_context(graph)
                        || *expression != body
                        || bindings != bs
                        || *applicability != "not_applicable"
                        || node.arguments != [instance, guard]
                        || parts.len() != 2
                        || parts[0].children != [guard]
                        || parts[0].location
                            != (Location::Law {
                                span: self.expression_span(graph, *guard_source)?,
                            })
                        || parts[0].residual
                            != guard_parts.last().ok_or("guard partがない")?.residual
                        || parts[0].value != self.evaluation(graph, guard)?.2
                        || parts[1].location
                            != (Location::Law {
                                span: self.expression_span(graph, body)?,
                            })
                        || parts[1].value.is_some()
                        || !parts[1].children.is_empty()
                        || parts[1].residual.is_some()
                        || graph.boolean(*value)? != Some(true)
                        || node.scope != graph.get(guard)?.scope
                        || node.support != graph.get(guard)?.support
                    {
                        return Err("非適用rowに架空body/値/範囲がある".into());
                    }
                    let value = value.ok_or("非適用値がない")?;
                    let producer = graph.get(value)?;
                    // 値自身の正当性に加え、このrowが実際に構成した適用値へ結ぶ。
                    if value.0 >= limit
                        || graph.context_at(value.0) != self.current_context(graph)
                        || producer.arguments != [instance, guard]
                    {
                        return Err("非適用rowの値が現在instance/guardのproducerでない".into());
                    }
                    self.validate_at(graph, producer, value.0)?;
                }
                Some(Payload::Proposition { instance: actual }) => {
                    let eval = *node.arguments.get(1).ok_or("非適用命題の元評価がない")?;
                    let application = graph.get(eval)?;
                    let Some(Payload::Evaluation {
                        value: Some(value),
                        applicability: "not_applicable",
                        ..
                    }) = &application.payload
                    else {
                        return Err("非適用命題の根拠が非適用Law評価でない".into());
                    };
                    if eval.0 >= limit
                        || application.ty != NodeType::Evaluation(Type::Bool)
                        || graph.context_at(eval.0) != self.current_context(graph)
                        || application.arguments != [instance, guard]
                        || graph.scalar(*value)? != &Scalar::Bool(true)
                    {
                        return Err("非適用命題の根拠が現在instance/guardの適用評価でない".into());
                    }
                    // 元guard/body Source・bindings・parts・値producerの既存照合も通す。
                    self.recheck_evaluation(graph, eval)?;
                    if node.ty != NodeType::Proposition
                        || !matches!(node.rule, Rule::Construction("proposition"))
                        || !reasons_equal(&node.reasons, &graph.get(guard)?.reasons)
                        || !node.judgment.as_ref().is_some_and(|j| {
                            reasons_equal(&j.reasons, &graph.get(guard).expect("既出guard").reasons)
                        })
                        || node.scope != graph.get(guard)?.scope
                        || node.support != graph.get(guard)?.support
                        || graph.context_at(instance.0) != self.current_context(graph)
                        || *actual != instance
                        || node.arguments != [instance, eval]
                        || node.judgment.as_ref().map(|j| j.status) != Some(Decision::Established)
                        || !node.evidence.is_empty()
                    {
                        return Err("非適用命題が元rowと違う".into());
                    }
                }
                _ => return Err("非適用rowの未定構成".into()),
            }
            return Ok(true);
        }
        Ok(false)
    }
    pub(in crate::observed) fn validate_family_answer(
        &self,
        graph: &Graph,
        request: &Request,
        answer: &Answer,
    ) -> Result<bool, ValidationFailure> {
        let Some(plan) = self.family_plan(request)? else {
            return Ok(false);
        };
        if plan.dependent
            && self.validate_dependent_family_unknown(graph, request, answer, &plan)?
        {
            return Ok(true);
        }
        let evaluation = *answer
            .outputs
            .get("evaluation")
            .ok_or("whole Answer評価がない")?;
        let node = graph.get(evaluation)?;
        let instance = *node.arguments.first().ok_or("whole Answer元Lawがない")?;
        if !self.family_template(graph, instance)? {
            return Err("whole Answerが実rowだけを返した".into());
        }
        self.recheck_evaluation(graph, evaluation)?;
        let claim = answer.claim.ok_or("whole Answer命題がない")?;
        self.validate_at(graph, graph.get(claim)?, claim.0)?;
        if graph.get(claim)?.arguments != [instance, evaluation]
            || answer.scope != node.scope
            || answer.status
                != family_decision(graph.boolean(self.evaluation(graph, evaluation)?.2)?)
        {
            return Err("whole Answerの元族・Scope・判断が違う".into());
        }
        Ok(true)
    }
}
pub(in crate::observed) fn family_decision(value: Option<bool>) -> Decision {
    match value {
        Some(true) => Decision::Established,
        Some(false) => Decision::Refuted,
        None => Decision::Undetermined,
    }
}

fn family_refs(a: &[NodeRef], b: &[NodeRef]) -> bool {
    a.len() == b.len()
        && a.iter()
            .enumerate()
            .all(|(i, r)| !a[..i].contains(r) && b.contains(r))
}

fn family_clean(node: &Node, rule: &str, reasons: &[Reason]) -> bool {
    matches!(node.rule,Rule::Construction(name) if name==rule)
        && node.evidence.is_empty()
        && node.judgment.is_none()
        && reasons_equal(&node.reasons, reasons)
}
